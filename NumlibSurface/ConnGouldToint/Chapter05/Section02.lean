import Mathlib.Basic.Real.Basic
import Numlib.Krylov.Lanczos
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# The Lanczos basis

Section 5.2 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter05

open Krylov

/-- Lemma 5.2.1. A basis of nested Krylov spaces can add the next vector using
the previous space and the image of its last vector. The argument uses the
successive spans and requires no normalization. -/
theorem lemma_5_2_1 {E : Type*} [AddCommGroup E] [Module ℝ E]
    (H : E →ₗ[ℝ] E) (q : ℕ → E) {k i : ℕ} (hi : i ≤ k)
    (hspan : ∀ j ≤ k + 1,
      subspace H (q 0) (j + 1) = Submodule.span ℝ (Set.range fun l : Fin (j + 1) => q l)) :
    q (i + 1) ∈ Submodule.span ℝ (Set.range fun l : Fin (i + 1) => q l) ⊔
      Submodule.span ℝ {H (q i)} := by
  let K := subspace H (q 0) (i + 1)
  let W := K ⊔ Submodule.span ℝ {H (q i)}
  have hK : K ≤ W := le_sup_left
  have hmap : K.map H ≤ W := by
    change (subspace H (q 0) (i + 1)).map H ≤ W
    rw [hspan i (by omega), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases (Nat.le_of_lt_succ j.isLt).lt_or_eq with hj | hj
    · have hqj : q j ∈ subspace H (q 0) i := by
        cases i with
        | zero => omega
        | succ l =>
          rw [hspan l (by omega)]
          exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      exact hK (map_subspace_le H (q 0) i ⟨_, hqj, rfl⟩)
    · apply Submodule.mem_sup_right
      change H (q j) ∈ Submodule.span ℝ {H (q i)}
      rw [hj]
      exact Submodule.mem_span_singleton_self _
  have hnext : subspace H (q 0) (i + 1 + 1) ≤ W := by
    rw [subspace_succ_eq_sup_map H (q 0) (Nat.succ_pos i)]
    exact sup_le hK hmap
  have hq : q (i + 1) ∈ subspace H (q 0) (i + 1 + 1) := by
    rw [hspan (i + 1) (by omega)]
    exact Submodule.subset_span ⟨⟨i + 1, Nat.lt_succ_self _⟩, rfl⟩
  simpa [W, K, hspan i (by omega)] using hnext hq


open scoped RealInnerProductSpace

/-- Algorithms 5.2.1 and 5.2.2 are the three-term symmetric Lanczos recurrence.
The initial unnormalized vector is the starting residual, and the preceding
basis vector at step zero is zero. -/
theorem algorithm_5_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {r₀ : E} (hr₀ : r₀ ≠ 0) (k : ℕ) :
    let q := Arnoldi.vec H r₀
    let y : ℕ → E := fun | 0 => r₀ | j + 1 => Arnoldi.w H r₀ j
    let prev : ℕ → E := fun | 0 => 0 | j + 1 => q j
    q k = ‖y k‖⁻¹ • y k ∧
      y (k + 1) = H (q k) - ⟪q k, H (q k)⟫ • q k - ‖y k‖ • prev k := by
  intro q y prev
  have hd (j : ℕ) : Lanczos.alpha H r₀ j = ⟪q j, H (q j)⟫ := by
    simp [Lanczos.alpha, Arnoldi.coeff, q]
  cases k with
  | zero =>
    refine ⟨by simpa using Arnoldi.vec_zero H r₀ hr₀, ?_⟩
    change Arnoldi.w H r₀ 0 = H (q 0) - ⟪q 0, H (q 0)⟫ • q 0 - ‖r₀‖ • (0 : E)
    have ha : H (q 0) = Lanczos.alpha H r₀ 0 • q 0 + Arnoldi.w H r₀ 0 := by
      have h := Lanczos.apply_vec_zero r₀ hH
      rw [Lanczos.beta, ← Arnoldi.w_eq_norm_smul_vec] at h
      simpa only [q, RCLike.ofReal_real_eq_id, id_eq] using h
    rw [← hd, ha, smul_zero, sub_zero]
    abel
  | succ j =>
    refine ⟨by simpa using Arnoldi.vec_succ_eq H r₀ j, ?_⟩
    change Arnoldi.w H r₀ (j + 1) = H (q (j + 1)) - ⟪q (j + 1), H (q (j + 1))⟫ •
      q (j + 1) - ‖Arnoldi.w H r₀ j‖ • q j
    simpa only [q, hd, Lanczos.beta, RCLike.ofReal_real_eq_id, id_eq] using Lanczos.w_succ_eq r₀ hH j


section MatrixLanczos

open Matrix WithLp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The columns of `Qₖ` are the Lanczos vectors through index `k`. -/
noncomputable def lanczosBasisMatrix (H : Matrix n n ℝ) (r₀ : n → ℝ) (k : ℕ) :
    Matrix n (Fin (k + 1)) ℝ :=
  Matrix.of fun i j => ofLp (Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀) j) i

/-- The three-term recurrence gives (5.2.14). The rank-one residual
is supported on the last column, and vanishes at breakdown. -/
theorem lanczos_relation_5_2_14 {H : Matrix n n ℝ} (hH : H.IsSymm)
    (r₀ : n → ℝ) (k : ℕ) :
    let A := toEuclideanLin H
    let b : EuclideanSpace ℝ n := toLp 2 r₀
    let Q := lanczosBasisMatrix H r₀ k
    let T := Lanczos.tridiag A b (k + 1)
    let qnext := ofLp (Arnoldi.vec A b (k + 1))
    H * Q - Q * T = Lanczos.beta A b k • Matrix.vecMulVec qnext (Pi.single (Fin.last k) 1) := by
  let A := toEuclideanLin H
  let b : EuclideanSpace ℝ n := toLp 2 r₀
  let Q := lanczosBasisMatrix H r₀ k
  let T := Lanczos.tridiag A b (k + 1)
  let q := Arnoldi.vec A b
  change H * Q - Q * T =
    Lanczos.beta A b k • Matrix.vecMulVec (ofLp (q (k + 1))) (Pi.single (Fin.last k) 1)
  have hQ (z : Fin (k + 1) → ℝ) :
      toLp 2 (Q *ᵥ z) = ∑ j : Fin (k + 1), z j • q j := by
    rw [← Matrix.toEuclideanLin_toLp, Matrix.toEuclideanLin_apply_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by
      change z j • toLp 2 (ofLp (q j)) = z j • q j
      rw [WithLp.toLp_ofLp]
  apply sub_eq_iff_eq_add'.mpr
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  apply WithLp.toLp_injective 2
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec z Q T,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, single_one_dotProduct,
    smul_smul, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_ofLp,
    ← Matrix.toEuclideanLin_toLp H, hQ, hQ]
  simpa only [A, b, T, q, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id,
    RCLike.ofReal_real_eq_id, id_eq] using Lanczos.apply_sum b hH.isSymmetric_toEuclideanLin k z

/-- The active Lanczos columns have Gram matrix equal to the identity,
and the next vector is orthogonal to them, as in (5.2.16). -/
theorem lanczos_orthonormal_5_2_16 (H : Matrix n n ℝ) (r₀ : n → ℝ) (k : ℕ)
    (hactive : ∀ j : Fin (k + 1), Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀) j ≠ 0) :
    let q := Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀)
    let Q := lanczosBasisMatrix H r₀ k
    Qᵀ * Q = 1 ∧ Qᵀ *ᵥ ofLp (q (k + 1)) = 0 := by
  let A := toEuclideanLin H
  let b : EuclideanSpace ℝ n := toLp 2 r₀
  let q := Arnoldi.vec A b
  let Q := lanczosBasisMatrix H r₀ k
  change Qᵀ * Q = 1 ∧ Qᵀ *ᵥ ofLp (q (k + 1)) = 0
  constructor
  · ext i j
    change ofLp (q i) ⬝ᵥ ofLp (q j) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) i j
    rw [← EuclideanSpace.inner_toLp_toLp_real, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    by_cases h : i = j
    · subst j
      rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_ne_zero A b (hactive i),
        one_pow, Matrix.one_apply_eq]
    · rw [Arnoldi.inner_vec_eq_zero A b (fun he => h (Fin.ext he)), Matrix.one_apply_ne h]
  · ext i
    change ofLp (q i) ⬝ᵥ ofLp (q (k + 1)) = 0
    rw [← EuclideanSpace.inner_toLp_toLp_real, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    exact Arnoldi.inner_vec_eq_zero A b (ne_of_lt i.isLt)

/-- Projecting (5.2.14) onto the active Lanczos basis gives (5.2.17). -/
theorem lanczos_projection_5_2_17 {H : Matrix n n ℝ} (hH : H.IsSymm)
    (r₀ : n → ℝ) (k : ℕ)
    (hactive : ∀ j : Fin (k + 1), Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀) j ≠ 0) :
    let Q := lanczosBasisMatrix H r₀ k
    Qᵀ * H * Q = Lanczos.tridiag (toEuclideanLin H) (toLp 2 r₀) (k + 1) := by
  let Q := lanczosBasisMatrix H r₀ k
  obtain ⟨horth, hperp⟩ := lanczos_orthonormal_5_2_16 H r₀ k hactive
  have hrec := sub_eq_iff_eq_add'.mp (lanczos_relation_5_2_14 hH r₀ k)
  change Qᵀ * H * Q = _
  rw [Matrix.mul_assoc, hrec, Matrix.mul_add, ← Matrix.mul_assoc, horth,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, hperp]
  simp

end MatrixLanczos

/-- Algorithms 5.2.3 and 5.2.4 are the same Lanczos iteration transported
through the factor of the preconditioner. The second recurrence uses the
dual vectors obtained by applying the preconditioner to the first. -/
theorem algorithms_5_2_3_5_2_4
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E ≃L[ℝ] F) {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {r₀ : E} (hr₀ : r₀ ≠ 0)
    (k : ℕ) :
    let S := R.symm.toContinuousLinearMap
    let L := R.toContinuousLinearMap
    let M := L.adjoint.comp L
    let Minv := S.comp S.adjoint
    let Hbar := S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap
    let rbar := S.adjoint r₀
    let qbar := Arnoldi.vec Hbar rbar
    let ybar : ℕ → F := fun | 0 => rbar | j + 1 => Arnoldi.w Hbar rbar j
    let q (j : ℕ) := S (qbar j)
    let y (j : ℕ) := S (ybar j)
    let w (j : ℕ) := M (q j)
    let t (j : ℕ) := M (y j)
    let prev : ℕ → E := fun | 0 => 0 | j + 1 => q j
    let prevW : ℕ → E := fun | 0 => 0 | j + 1 => w j
    let γ := ‖ybar k‖
    let δ := ⟪q k, H (q k)⟫
    y 0 = Minv r₀ ∧ t 0 = r₀ ∧
      γ = Real.sqrt ⟪y k, M (y k)⟫ ∧ q k = γ⁻¹ • y k ∧
      y (k + 1) = Minv (H (q k)) - δ • q k - γ • prev k ∧
      y k = Minv (t k) ∧ γ = Real.sqrt ⟪t k, y k⟫ ∧ w k = γ⁻¹ • t k ∧
      t (k + 1) = H (q k) - δ • w k - γ • prevW k := by
  intro S L M Minv Hbar rbar qbar ybar q y w t prev prevW γ δ
  have hLS (z : F) : L (S z) = z := R.apply_symm_apply z
  have hSL (z : E) : S (L z) = z := R.symm_apply_apply z
  have hSadL (z : F) : S.adjoint (L.adjoint z) = z := by
    have he : L.comp S = ContinuousLinearMap.id ℝ F := ContinuousLinearMap.ext hLS
    have he' := congrArg ContinuousLinearMap.adjoint he
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at he'
    exact congrArg (fun B : F →L[ℝ] F ↦ B z) he'
  have hLadS (z : E) : L.adjoint (S.adjoint z) = z := by
    have he : S.comp L = ContinuousLinearMap.id ℝ E := ContinuousLinearMap.ext hSL
    have he' := congrArg ContinuousLinearMap.adjoint he
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at he'
    exact congrArg (fun B : E →L[ℝ] E ↦ B z) he'
  have hMS (z : F) : M (S z) = L.adjoint z := by
    change L.adjoint (L (S z)) = _
    rw [hLS]
  have hMinv (z : E) : Minv (M z) = z := by
    change S (S.adjoint (L.adjoint (L z))) = z
    rw [hSadL, hSL]
  have hMMinv (z : E) : M (Minv z) = z := by
    change M (S (S.adjoint z)) = z
    rw [hMS, hLadS]
  have hsym : Hbar.IsSymmetric := by
    intro u v
    change ⟪S.adjoint (H (S u)), v⟫ = ⟪u, S.adjoint (H (S v))⟫
    rw [S.adjoint_inner_left, S.adjoint_inner_right, hH]
  have hrbar : rbar ≠ 0 := by
    intro h
    have he := hLadS r₀
    change L.adjoint rbar = r₀ at he
    rw [h, map_zero] at he
    exact hr₀ he.symm
  obtain ⟨hqbar, hybar⟩ := algorithm_5_2_1 hsym hrbar k
  let prevBar : ℕ → F := fun | 0 => 0 | j + 1 => qbar j
  change qbar k = γ⁻¹ • ybar k at hqbar
  change ybar (k + 1) = Hbar (qbar k) - ⟪qbar k, Hbar (qbar k)⟫ • qbar k -
    γ • prevBar k at hybar
  have hδ : ⟪qbar k, Hbar (qbar k)⟫ = δ := S.adjoint_inner_right _ _
  have hprev (j : ℕ) : S (prevBar j) = prev j := by
    cases j <;> simp [prevBar, prev, q]
  have hprevW (j : ℕ) : M (prev j) = prevW j := by
    cases j <;> simp [prevW, prev, w]
  have hy (j : ℕ) : Minv (t j) = y j := hMinv _
  have hq : q k = γ⁻¹ • y k := by
    change S (qbar k) = _
    rw [hqbar, map_smul]
  have hyrec : y (k + 1) = Minv (H (q k)) - δ • q k - γ • prev k := by
    change S (ybar (k + 1)) = _
    rw [hybar, map_sub, map_sub, map_smul, map_smul, hδ, hprev]
    rfl
  have hnorm : γ = Real.sqrt ⟪y k, M (y k)⟫ := by
    change ‖ybar k‖ = Real.sqrt ⟪S (ybar k), M (S (ybar k))⟫
    rw [hMS, L.adjoint_inner_right, hLS, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨rfl, hMMinv r₀, hnorm, hq, hyrec, (hy k).symm, ?_, ?_, ?_⟩
  · simpa only [t, real_inner_comm (M (y k))] using hnorm
  · change M (q k) = _
    rw [hq, map_smul]
  · change M (y (k + 1)) = _
    rw [hyrec, map_sub, map_sub, map_smul, map_smul, hMMinv, hprevW]


/-- The transported nonzero Lanczos vectors are orthonormal in the
preconditioner inner product, as in (5.2.51). -/
theorem preconditioned_lanczos_orthonormal_5_2_51
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (r₀ : E) (i j : ℕ) :
    let S := R.symm.toContinuousLinearMap
    let L := R.toContinuousLinearMap
    let M := L.adjoint.comp L
    let Hbar := S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap
    let qbar := Arnoldi.vec Hbar (S.adjoint r₀)
    let q (k : ℕ) := S (qbar k)
    (i ≠ j → ⟪q i, M (q j)⟫ = 0) ∧ (qbar i ≠ 0 → ⟪q i, M (q i)⟫ = 1) := by
  intro S L M Hbar qbar q
  have hinner (a b : F) : ⟪S a, M (S b)⟫ = ⟪a, b⟫ := by
    change ⟪S a, L.adjoint (L (S b))⟫ = _
    rw [L.adjoint_inner_right]
    change ⟪R (R.symm a), R (R.symm b)⟫ = _
    rw [R.apply_symm_apply, R.apply_symm_apply]
  refine ⟨fun hij ↦ ?_, fun hi ↦ ?_⟩
  · change ⟪S (qbar i), M (S (qbar j))⟫ = 0
    rw [hinner]
    exact Arnoldi.inner_vec_eq_zero Hbar (S.adjoint r₀) hij
  · change ⟪S (qbar i), M (S (qbar i))⟫ = 1
    rw [hinner, real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_ne_zero Hbar
      (S.adjoint r₀) hi, one_pow]

open scoped Matrix in
/-- The Lanczos matrix relation for the transformed system gives the
preconditioned relation (5.2.52). Orthonormality of the transformed basis
and orthogonality of the residual column then give the reduced matrix
identity (5.2.53). The vector `e` is the final coordinate vector. -/
theorem preconditioned_lanczos_matrix_relations_5_2_52_53
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (H R Rinv : Matrix n n ℝ) (Qbar : Matrix n m ℝ) (T : Matrix m m ℝ)
    (qbar : n → ℝ) (e : m → ℝ) (γ : ℝ)
    (hL : Rinv * R = 1) (hR : R * Rinv = 1)
    (hLanczos : (Rinvᵀ * H * Rinv) * Qbar - Qbar * T = γ • Matrix.vecMulVec qbar e)
    (horth : Qbarᵀ * Qbar = 1) (hperp : Qbarᵀ *ᵥ qbar = 0) :
    let Q := Rinv * Qbar
    let M := Rᵀ * R
    H * Q - M * Q * T = γ • Matrix.vecMulVec (Rᵀ *ᵥ qbar) e ∧ Qᵀ * H * Q = T := by
  let Hbar := Rinvᵀ * H * Rinv
  let Q := Rinv * Qbar
  have htrans : Rᵀ * Rinvᵀ = 1 := by
    rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
  have hleft : Rᵀ * (Hbar * Qbar) = H * Q := by
    change Rᵀ * ((Rinvᵀ * H * Rinv) * Qbar) = H * (Rinv * Qbar)
    simp only [← Matrix.mul_assoc, htrans, Matrix.one_mul]
  have hMQ : (Rᵀ * R) * Q = Rᵀ * Qbar := by
    change (Rᵀ * R) * (Rinv * Qbar) = Rᵀ * Qbar
    calc
      _ = Rᵀ * ((R * Rinv) * Qbar) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.one_mul]
  change H * Q - (Rᵀ * R) * Q * T = _ ∧ Qᵀ * H * Q = _
  constructor
  · have hr := congrArg (fun X : Matrix n m ℝ ↦ Rᵀ * X) hLanczos
    change Rᵀ * (Hbar * Qbar - Qbar * T) = _ at hr
    rw [Matrix.mul_sub, hleft, ← Matrix.mul_assoc Rᵀ Qbar T, ← hMQ,
      Matrix.mul_smul, Matrix.mul_vecMulVec] at hr
    exact hr
  · have hsum : Hbar * Qbar = Qbar * T + γ • Matrix.vecMulVec qbar e :=
      sub_eq_iff_eq_add'.mp hLanczos
    calc
      Qᵀ * H * Q = Qbarᵀ * (Hbar * Qbar) := by
        change (Rinv * Qbar)ᵀ * H * (Rinv * Qbar) =
          Qbarᵀ * ((Rinvᵀ * H * Rinv) * Qbar)
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = T := by
        rw [hsum, Matrix.mul_add, ← Matrix.mul_assoc Qbarᵀ Qbar T, horth,
          Matrix.one_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, hperp]
        simp

open Matrix WithLp in
/-- Applying (5.2.14) and (5.2.16) to the transformed matrix gives the
preconditioned matrix identities directly from the Lanczos run. -/
theorem preconditioned_lanczos_run_relations_5_2_52_53
    {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℝ} (hH : H.IsSymm)
    (R Rinv : Matrix n n ℝ) (r₀ : n → ℝ) (k : ℕ)
    (hL : Rinv * R = 1) (hR : R * Rinv = 1)
    (hactive : ∀ j : Fin (k + 1),
      Arnoldi.vec (toEuclideanLin (Rinvᵀ * H * Rinv)) (toLp 2 (Rinvᵀ *ᵥ r₀)) j ≠ 0) :
    let Hbar := Rinvᵀ * H * Rinv
    let rbar := Rinvᵀ *ᵥ r₀
    let A := toEuclideanLin Hbar
    let b : EuclideanSpace ℝ n := toLp 2 rbar
    let Q := Rinv * lanczosBasisMatrix Hbar rbar k
    let M := Rᵀ * R
    let T := Lanczos.tridiag A b (k + 1)
    let qnext := ofLp (Arnoldi.vec A b (k + 1))
    H * Q - M * Q * T =
        Lanczos.beta A b k • Matrix.vecMulVec (Rᵀ *ᵥ qnext) (Pi.single (Fin.last k) 1) ∧
      Qᵀ * H * Q = T := by
  let Hbar := Rinvᵀ * H * Rinv
  let rbar := Rinvᵀ *ᵥ r₀
  let A := toEuclideanLin Hbar
  let b : EuclideanSpace ℝ n := toLp 2 rbar
  have hsym : Hbar.IsSymm := by
    change (Rinvᵀ * H * Rinv)ᵀ = Rinvᵀ * H * Rinv
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.eq,
      Matrix.mul_assoc]
  obtain ⟨horth, hperp⟩ := lanczos_orthonormal_5_2_16 Hbar rbar k hactive
  exact preconditioned_lanczos_matrix_relations_5_2_52_53 H R Rinv
    (lanczosBasisMatrix Hbar rbar k) (Lanczos.tridiag A b (k + 1))
    (ofLp (Arnoldi.vec A b (k + 1))) (Pi.single (Fin.last k) 1) (Lanczos.beta A b k)
    hL hR (lanczos_relation_5_2_14 hsym rbar k) horth hperp

end ConnGouldToint.Chapter05
