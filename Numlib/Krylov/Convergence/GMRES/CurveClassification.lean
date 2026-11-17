/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRESCurve
import Numlib.Krylov.Decomposition
import Numlib.LinearAlgebra.Matrix.QR

/-!
# QR coordinates for prescribed GMRES curves

The columns of a full-rank mapped Krylov matrix carry the companion shift.
An orthonormal basis from its QR factorization gives the GMRES residual norm
at each step through the unused coordinates of the right-hand side.
-/

open Finset Matrix Polynomial
open scoped Matrix

namespace Krylov

variable {n : ℕ}

private abbrev Mat (n : ℕ) := Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
private abbrev Vec (n : ℕ) := Fin (n + 1) → ℂ

private theorem companionLastColumn_mulVec_single (p : ℂ[X]) (j : Fin n) :
    Matrix.companionLastColumn n p *ᵥ Pi.single j.castSucc 1 = Pi.single j.succ 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, Matrix.companionLastColumn_castSucc]
  by_cases hij : i = j.succ
  · subst i
    simp
  · simp [hij]

private theorem krylovMatrix_companionLastColumn (p : ℂ[X]) :
    Matrix.krylovMatrix (Matrix.companionLastColumn n p) (Pi.single 0 1) (n + 1) = 1 := by
  have hp (i : Fin (n + 1)) : (Matrix.companionLastColumn n p) ^ i.val *ᵥ Pi.single 0 1 =
      Pi.single i 1 := by
    induction i using Fin.induction with
    | zero => rw [Fin.val_zero, pow_zero, Matrix.one_mulVec]
    | succ i hi =>
      rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec, ← Fin.val_castSucc i, hi,
        companionLastColumn_mulVec_single]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [Matrix.mulVec_single_one, Matrix.col_krylovMatrix, Matrix.one_mulVec, hp]

private theorem pow_mulVec_eq_neg_sum_of_charpoly {A : Mat n} {p : ℂ[X]}
    (hp : A.charpoly = p) (v : Vec n) :
    A ^ (n + 1) *ᵥ v = -∑ i : Fin (n + 1), p.coeff i.val • (A ^ i.val *ᵥ v) := by
  have hd : p.natDegree = n + 1 := by
    rw [← hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have htop : p.coeff (n + 1) = 1 := by
    rw [← hd]
    exact (hp ▸ A.charpoly_monic).coeff_natDegree
  have h := Matrix.aeval_self_charpoly A
  rw [hp, Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, htop, one_smul] at h
  have he : A ^ (n + 1) = -∑ i ∈ Finset.range (n + 1), p.coeff i • A ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  rw [he, Matrix.neg_mulVec, Matrix.sum_mulVec, ← Fin.sum_univ_eq_sum_range]
  simp_rw [Matrix.smul_mulVec]

private theorem mul_krylovMatrix_eq_mul_companionLastColumn {A : Mat n} {p : ℂ[X]}
    (hp : A.charpoly = p) (v : Vec n) :
    A * Matrix.krylovMatrix A v (n + 1) =
      Matrix.krylovMatrix A v (n + 1) * Matrix.companionLastColumn n p := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    change (A * _).col (Fin.last n) i = (_ * Matrix.companionLastColumn n p).col (Fin.last n) i
    rw [Matrix.col_mul_krylovMatrix, Fin.val_last, col_mul_eq_mulVec_col,
      pow_mulVec_eq_neg_sum_of_charpoly hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.companionLastColumn_last,
      Matrix.krylovMatrix_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mul_neg, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => congrArg Neg.neg (mul_comm _ _)
  | cast j =>
    change (A * _).col j.castSucc i = (_ * Matrix.companionLastColumn n p).col j.castSucc i
    rw [Matrix.col_mul_krylovMatrix, Matrix.col_mul_eq_mulVec_col,
      ← Matrix.mulVec_single_one, companionLastColumn_mulVec_single, Matrix.mulVec_single_one,
      Matrix.col_krylovMatrix]
    rfl

private theorem krylovMatrix_eq_of_intertwine {A B C : Mat n} (h : A * B = B * C)
    (v : Vec n) :
    Matrix.krylovMatrix A (B *ᵥ v) (n + 1) = B * Matrix.krylovMatrix C v (n + 1) := by
  have hpow (k : ℕ) : A ^ k * B = B * C ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' A, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc, pow_succ']
  ext i j
  change (Matrix.krylovMatrix A (B *ᵥ v) _).col j i =
    (B * Matrix.krylovMatrix C v _).col j i
  rw [Matrix.col_krylovMatrix, Matrix.col_mul_eq_mulVec_col, Matrix.col_krylovMatrix,
    Matrix.mulVec_mulVec, hpow, ← Matrix.mulVec_mulVec]

private theorem span_prefix_eq_of_qr {A Q T : Mat n} {b : Vec n}
    (hqr : Matrix.IsQR (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)) Q T)
    (hBu : IsUnit (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)))
    (k : ℕ) (hk : k ≤ n + 1) :
    Submodule.span ℂ ((fun i => WithLp.toLp 2 (Q.col i)) '' {i | i.val < k}) =
      (subspace (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) k).map (Matrix.toEuclideanLin A) := by
  let L := Matrix.toEuclideanLin A
  let u := WithLp.toLp 2 b
  have hspan := (hqr.span_col_prefix_eq (Matrix.linearIndependent_col_iff_isUnit.2 hBu)
    le_rfl hk).1
  let e := (WithLp.linearEquiv 2 ℂ (Vec n)).symm.toLinearMap
  have hspan' := congrArg (fun S : Submodule ℂ (Vec n) => S.map e) hspan
  simp only [Submodule.map_span, ← Set.range_comp] at hspan'
  have hflag :
      (subspace L u k).map L = Submodule.span ℂ
        (Set.range fun j : Fin k => WithLp.toLp 2
          ((Matrix.krylovMatrix A (A *ᵥ b) (n + 1)).col (Fin.castLE hk j))) := by
    rw [map_subspace_of_semiconj (N := L) (B := L) (C := L) (fun _ => rfl)]
    rw [show L u = WithLp.toLp 2 (A *ᵥ b) from rfl, ← Matrix.range_krylovMatrix,
       Matrix.range_toEuclideanLin_eq_span_col]
    rfl
  rw [hflag]
  refine Eq.trans ?_ hspan'.symm
  congr 1
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hk j, j.isLt, rfl⟩

private theorem norm_sq_residual_of_qr {A Q T : Mat n} {b : Vec n}
    (hqr : Matrix.IsQR (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)) Q T)
    (hBu : IsUnit (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)))
    {k : ℕ} (hk : k ≤ n + 1) {x : EuclideanSpace ℂ (Fin (n + 1))}
    (hx : IsMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 k x) :
    ‖WithLp.toLp 2 b - Matrix.toEuclideanLin A x‖ ^ 2 =
      ∑ i : Fin (n + 1) with k ≤ i.val, ‖(Qᴴ *ᵥ b) i‖ ^ 2 := by
  let w (i : Fin (n + 1)) := WithLp.toLp 2 (Q.col i)
  have hQH : Qᴴ * Q = 1 := Unitary.star_mul_self_of_mem hqr.mem_unitaryGroup
  have hQQH : Q * Qᴴ = 1 := Unitary.mul_star_self_of_mem hqr.mem_unitaryGroup
  have hw : Orthonormal ℂ w := Matrix.conjTranspose_mul_self_eq_one_iff_orthonormal.1 hQH
  have hs := span_prefix_eq_of_qr hqr hBu k hk
  have hr := hx.residual_eq_sub_sum_prefix hw (by simpa using hs)
  simp only [map_zero, sub_zero] at hr
  let L := Matrix.toEuclideanLinearIsometryEquiv hQH hQQH
  let η := WithLp.toLp 2 (Qᴴ *ᵥ b)
  let v := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
  have hL (i : Fin (n + 1)) : L (v i) = w i := by
    change Matrix.toEuclideanLin Q (v i) = _
    rw [EuclideanSpace.basisFun_apply]
    change WithLp.toLp 2 (Q *ᵥ Pi.single i 1) = _
    rw [Matrix.mulVec_single_one]
  have heta : L η = WithLp.toLp 2 b := by
    change WithLp.toLp 2 (Q *ᵥ (Qᴴ *ᵥ b)) = _
    rw [Matrix.mulVec_mulVec, hQQH, Matrix.one_mulVec]
  rw [hr, ← heta]
  simp_rw [← hL, L.inner_map_map, ← OrthonormalBasis.repr_apply_apply,
    show ∀ i, v.repr η i = η i from fun _ => rfl, ← map_smul L, ← map_sum L, ← map_sub L,
    L.norm_map]
  exact norm_sq_sub_coordinate_prefix η k

private theorem isUnit_of_charpoly_eval_zero_ne_zero {A : Mat n} {p : ℂ[X]}
    (hp : A.charpoly = p) (hp0 : p.eval 0 ≠ 0) : IsUnit A := by
  rw [← hp, Matrix.eval_charpoly, map_zero, zero_sub, Matrix.det_neg] at hp0
  exact (Matrix.isUnit_iff_isUnit_det A).2
    (isUnit_iff_ne_zero.2 fun hz => hp0 (by rw [hz, mul_zero]))

private theorem conjTranspose_eq_inv_of_unitary {W : Mat n}
    (hW : W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Wᴴ = W⁻¹ := by
  have hu := Matrix.isUnit_of_mem_unitaryGroup hW
  have he : Wᴴ * W = 1 := Unitary.star_mul_self_of_mem hW
  calc Wᴴ = Wᴴ * (W * W⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.mul_one]
    _ = W⁻¹ := by rw [← Matrix.mul_assoc, he, Matrix.one_mul]

private theorem isUnit_mappedKrylov_of_residual_ne_zero {A : Mat n} {b : Vec n}
    (hA : IsUnit A) {x : EuclideanSpace ℂ (Fin (n + 1))}
    (hx : IsMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 n x)
    (hres : WithLp.toLp 2 b - Matrix.toEuclideanLin A x ≠ 0) :
    IsUnit (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)) := by
  let L := Matrix.toEuclideanLin A
  let u := WithLp.toLp 2 b
  have hinj : Function.Injective L := by
    intro x y h
    apply WithLp.ofLp_injective
    apply Matrix.mulVec_injective_iff_isUnit.2 hA
    exact congrArg WithLp.ofLp h
  have hg : grade L u = n + 1 := by
    have hle := grade_le_finrank L u
    rw [finrank_euclideanSpace_fin] at hle
    have hn : ¬ grade L u ≤ n := by
      intro hn
      have he := hx.apply_eq_of_grade_le (by simpa using hn) hinj.injOn
      exact hres (sub_eq_zero.mpr he.symm)
    omega
  have hK : IsUnit (Matrix.krylovMatrix A b (n + 1)) := by
    have he := (grade_eq_rank_krylovMatrix A b).symm.trans hg
    rw [Fintype.card_fin] at he
    exact Matrix.isUnit_of_rank_eq_card (by simpa only [Fintype.card_fin] using he)
  have he : Matrix.krylovMatrix A (A *ᵥ b) (n + 1) =
      A * Matrix.krylovMatrix A b (n + 1) := by
    ext i j
    change (Matrix.krylovMatrix A (A *ᵥ b) _).col j i =
      (A * Matrix.krylovMatrix A b _).col j i
    rw [Matrix.col_krylovMatrix, Matrix.col_mul_krylovMatrix, mulVec_mulVec, pow_succ]
  rw [he]
  exact hA.mul hK

private theorem norm_eq_of_eq_tail_sums {η h : Vec n}
    (hs : ∀ k : Fin (n + 1),
      (∑ i : Fin (n + 1) with k.val ≤ i.val, ‖η i‖ ^ 2) =
      ∑ i : Fin (n + 1) with k.val ≤ i.val, ‖h i‖ ^ 2) (i : Fin (n + 1)) :
    ‖η i‖ = ‖h i‖ := by
  classical
  have hsplit : insert i (Finset.univ.filter (fun j : Fin (n + 1) => i.val + 1 ≤ j.val)) =
      Finset.univ.filter (fun j : Fin (n + 1) => i.val ≤ j.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hout : i ∉ Finset.univ.filter (fun j : Fin (n + 1) => i.val + 1 ≤ j.val) := by simp
  have he := hs i
  rw [← hsplit, Finset.sum_insert hout, Finset.sum_insert hout] at he
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  by_cases hi : i.val + 1 < n + 1
  · have hs' := hs ⟨i.val + 1, hi⟩
    dsimp only at hs'
    linarith
  · have hz : Finset.univ.filter (fun j : Fin (n + 1) => i.val + 1 ≤ j.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro j _ hj
      exact hi (hj.trans_lt j.isLt)
    simp only [hz, Finset.sum_empty, add_zero] at he
    exact he

private theorem exists_unitary_diagonal_mulVec {η h : Vec n}
    (hnorm : ∀ i, ‖η i‖ = ‖h i‖) :
    ∃ d : Vec n, Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ ∧
      Matrix.diagonal d *ᵥ h = η := by
  classical
  let d (i : Fin (n + 1)) := if h i = 0 then 1 else η i / h i
  have hd (i : Fin (n + 1)) : ‖d i‖ = 1 := by
    by_cases hi : h i = 0
    · simp [d, hi]
    · simp [d, hi, hnorm i, (norm_pos_iff.2 hi).ne']
  have hu : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    have he (i : Fin (n + 1)) : star (d i) * d i = 1 := by
      change (starRingEnd ℂ (d i)) * d i = 1
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hd]
      norm_num
    change Matrix.diagonal (fun i => star (d i) * d i) = 1
    rw [show (fun i => star (d i) * d i) = fun _ => 1 from funext he, Matrix.diagonal_one]
  refine ⟨d, hu, ?_⟩
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : h i = 0
  · have hη : η i = 0 := norm_eq_zero.mp (by simp [hnorm i, hi])
    simp [hi, hη]
  · simp [d, hi]

/-- A complex matrix with a prescribed nonzero characteristic polynomial at the
origin and a prescribed positive GMRES curve admits the constrained upper
triangular companion similarity. This is the QR construction using the
mapped Krylov columns. -/
theorem companion_of_gmres_curve {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {b s : Fin (n + 1) → ℂ} {p : ℂ[X]} (hp : A.charpoly = p) (hp0 : p.eval 0 ≠ 0)
    (hs : Matrix.companionLastColumn n p *ᵥ s = Pi.single 0 1)
    (f : Fin (n + 1) → ℝ) (hf : Antitone f) (hpos : 0 < f (Fin.last n))
    (x : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)))
    (hx : ∀ k, IsMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 k.val (x k))
    (hr : ∀ k, ‖WithLp.toLp 2 b - Matrix.toEuclideanLin A (x k)‖ = f k) :
    ∃ W T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ ∧ T.IsUpperTriangular ∧ IsUnit T ∧
      T *ᵥ s = WithLp.ofLp (gmresCurveCoordinates f) ∧
      b = W *ᵥ WithLp.ofLp (gmresCurveCoordinates f) ∧
      A = W * T * Matrix.companionLastColumn n p * T⁻¹ * Wᴴ := by
  let C := Matrix.companionLastColumn n p
  let B := Matrix.krylovMatrix A (A *ᵥ b) (n + 1)
  let h := WithLp.ofLp (gmresCurveCoordinates f)
  have hAu := isUnit_of_charpoly_eval_zero_ne_zero hp hp0
  have hn : WithLp.toLp 2 b - Matrix.toEuclideanLin A (x (Fin.last n)) ≠ 0 := by
    exact norm_pos_iff.1 ((hr (Fin.last n)).symm ▸ hpos)
  have hBu : IsUnit B := isUnit_mappedKrylov_of_residual_ne_zero hAu (hx (Fin.last n)) hn
  obtain ⟨Q, R, hqr⟩ := Matrix.exists_isQR B
  have hQu := Matrix.isUnit_of_mem_unitaryGroup hqr.mem_unitaryGroup
  have hRu : IsUnit R := by
    have hQRu : IsUnit (Q * R) := hqr.mul_eq.symm ▸ hBu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, isUnit_iff_ne_zero] at hQRu
    exact (Matrix.isUnit_iff_isUnit_det R).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hQRu))
  have hRt : R.IsUpperTriangular := fun i j hij => hqr.apply_eq_zero i j hij
  let η := Qᴴ *ᵥ b
  have hη (k : Fin (n + 1)) :
      (∑ i : Fin (n + 1) with k.val ≤ i.val, ‖η i‖ ^ 2) =
      ∑ i : Fin (n + 1) with k.val ≤ i.val, ‖h i‖ ^ 2 := by
    rw [← norm_sq_residual_of_qr hqr hBu k.isLt.le (hx k), hr k]
    exact (sum_norm_sq_gmresCurveCoordinates f hf hpos.le k).symm
  obtain ⟨d, hd, hdη⟩ := exists_unitary_diagonal_mulVec (norm_eq_of_eq_tail_sums hη)
  let D := Matrix.diagonal d
  let W := Q * D
  let T := Dᴴ * R
  have hW : W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
    mul_mem hqr.mem_unitaryGroup hd
  have hT : T.IsUpperTriangular := by
    intro i j hij
    change ((Matrix.diagonal d)ᴴ * R) i j = 0
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, hRt hij, mul_zero]
  have hTu : IsUnit T :=
    (Matrix.isUnit_of_mem_unitaryGroup (Unitary.star_mem hd)).mul hRu
  have hB : W * T = B := by
    change Q * D * (Dᴴ * R) = B
    rw [Matrix.mul_assoc Q D, ← Matrix.mul_assoc D,
      show D * Dᴴ = 1 from Unitary.mul_star_self_of_mem hd, Matrix.one_mul, hqr.mul_eq]
  have hb : b = W *ᵥ h := by
    change b = (Q * D) *ᵥ h
    rw [← Matrix.mulVec_mulVec, hdη, Matrix.mulVec_mulVec,
      show Q * Qᴴ = 1 from Unitary.mul_star_self_of_mem hqr.mem_unitaryGroup, Matrix.one_mulVec]
  have hAB : A * B = B * C := mul_krylovMatrix_eq_mul_companionLastColumn hp _
  have hBs : B *ᵥ s = b := by
    apply Matrix.mulVec_injective_iff_isUnit.2 hAu
    rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_single_one]
    simp [B, Matrix.col_krylovMatrix]
  refine ⟨W, T, hW, hT, hTu, ?_, hb, ?_⟩
  · apply Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_of_mem_unitaryGroup hW)
    rw [Matrix.mulVec_mulVec, hB, hBs, ← hb]
  · have hBd := (Matrix.isUnit_iff_isUnit_det B).1 hBu
    have he := congrArg (fun M => M * B⁻¹) hAB
    rw [Matrix.mul_assoc A B, Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one] at he
    rw [he, ← hB, Matrix.mul_inv_rev, ← conjTranspose_eq_inv_of_unitary hW, ← Matrix.mul_assoc]

private theorem isQR_mappedKrylov_of_companion
    {A W T : Mat n} {b s : Vec n} {p : ℂ[X]}
    (hW : W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hT : T.IsUpperTriangular) (hTu : IsUnit T)
    (hs : Matrix.companionLastColumn n p *ᵥ s = Pi.single 0 1)
    (hbs : (W * T) *ᵥ s = b)
    (hA : A = W * T * Matrix.companionLastColumn n p * T⁻¹ * Wᴴ) :
    A.charpoly = (Matrix.companionLastColumn n p).charpoly ∧
      IsUnit (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)) ∧
      Matrix.IsQR (Matrix.krylovMatrix A (A *ᵥ b) (n + 1)) W T := by
  let B := W * T
  let C := Matrix.companionLastColumn n p
  have hBu : IsUnit B := (Matrix.isUnit_of_mem_unitaryGroup hW).mul hTu
  have hBd := (Matrix.isUnit_iff_isUnit_det B).1 hBu
  have hA' : A = B * C * B⁻¹ := by
    rw [hA, conjTranspose_eq_inv_of_unitary hW, Matrix.mul_inv_rev, ← Matrix.mul_assoc]
  have hAB : A * B = B * C := by
    rw [hA', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBd, Matrix.mul_one]
  have hAb : A *ᵥ b = B *ᵥ Pi.single 0 1 := by
    rw [← hbs, Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, hs]
  have hB : Matrix.krylovMatrix A (A *ᵥ b) (n + 1) = B := by
    rw [hAb, krylovMatrix_eq_of_intertwine hAB, krylovMatrix_companionLastColumn, Matrix.mul_one]
  refine ⟨Matrix.charpoly_eq_of_mul_eq_mul hBd.ne_zero hAB, hB.symm ▸ hBu, ?_⟩
  exact ⟨hW, fun _ _ hij => hT (by simpa using hij), hB.symm⟩

/-- A unitary and upper triangular companion similarity with $Ts=h$,
$Cs=e_0$, and right-hand side $Wh$ realizes the prescribed GMRES curve.
The coordinates $h$ are the square roots of the successive differences of
the squared desired residual norms, including the final drop to zero. -/
theorem gmres_curve_of_companion {A W T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {b s : Fin (n + 1) → ℂ} {p : ℂ[X]} (hp : p.Monic) (hd : p.natDegree = n + 1)
    (f : Fin (n + 1) → ℝ) (hf : Antitone f) (hpos : 0 ≤ f (Fin.last n))
    (hW : W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hT : T.IsUpperTriangular) (hTu : IsUnit T)
    (hs : Matrix.companionLastColumn n p *ᵥ s = Pi.single 0 1)
    (hTs : T *ᵥ s = WithLp.ofLp (gmresCurveCoordinates f))
    (hb : b = W *ᵥ WithLp.ofLp (gmresCurveCoordinates f))
    (hA : A = W * T * Matrix.companionLastColumn n p * T⁻¹ * Wᴴ) :
    A.charpoly = p ∧
      ∀ (k : Fin (n + 1)) (x : EuclideanSpace ℂ (Fin (n + 1))),
        IsMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 k.val x →
        ‖WithLp.toLp 2 b - Matrix.toEuclideanLin A x‖ = f k := by
  have hbs : (W * T) *ᵥ s = b := by rw [← Matrix.mulVec_mulVec, hTs, hb]
  obtain ⟨hchar, hBu, hqr⟩ := isQR_mappedKrylov_of_companion hW hT hTu hs hbs hA
  rw [Matrix.charpoly_companionLastColumn n p hp hd] at hchar
  refine ⟨hchar, fun k x hx => ?_⟩
  have hη : Wᴴ *ᵥ b = WithLp.ofLp (gmresCurveCoordinates f) := by
    rw [hb, Matrix.mulVec_mulVec,
      show Wᴴ * W = 1 from Unitary.star_mul_self_of_mem hW, Matrix.one_mulVec]
  apply (sq_eq_sq₀ (norm_nonneg _) (hpos.trans (hf (Fin.le_last k)))).mp
  rw [norm_sq_residual_of_qr hqr hBu k.isLt.le hx, hη]
  exact sum_norm_sq_gmresCurveCoordinates f hf hpos k

/-- The vector of negated nonconstant coefficients of the polynomial $p/p(0)$,
ordered by increasing degree. These are the coefficients $\xi_j$ in
$p(z)/p(0)=1-\sum_{j=1}^{n+1}\xi_j z^j$ for monic $p$ of degree $n+1$. -/
noncomputable def gmresCompanionCoefficients (n : ℕ) (p : ℂ[X]) : Fin (n + 1) → ℂ :=
  fun i => -p.coeff (i.val + 1) / p.coeff 0

/-- The normalized coefficients are the first column of the inverse of the
last-column companion matrix, since $Cs=e_0$. -/
theorem companionLastColumn_mul_gmresCompanionCoefficients (n : ℕ) (p : ℂ[X])
    (hp : p.Monic) (hd : p.natDegree = n + 1) (h0 : p.eval 0 ≠ 0) :
    Matrix.companionLastColumn n p *ᵥ gmresCompanionCoefficients n p = Pi.single 0 1 := by
  have h0' : p.coeff 0 ≠ 0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  have htop : p.coeff (n + 1) = 1 := hd ▸ hp.coeff_natDegree
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Matrix.companionLastColumn_castSucc,
    Matrix.companionLastColumn_last, ite_mul, one_mul, zero_mul]
  have hlast : gmresCompanionCoefficients n p (Fin.last n) = -1 / p.coeff 0 := by
    simp [gmresCompanionCoefficients, htop]
  rw [hlast]
  induction i using Fin.cases with
  | zero =>
    simp only [Ne.symm (Fin.succ_ne_zero _), ↓reduceIte, Finset.sum_const_zero, zero_add,
      Pi.single_eq_same, Fin.val_zero]
    field_simp
  | succ i =>
    simp only [Fin.succ_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Fin.val_succ,
      Pi.single_eq_of_ne (Fin.succ_ne_zero _), gmresCompanionCoefficients,
      Fin.val_castSucc]
    ring

/-- The last-column companion matrix of a monic polynomial of the matching
degree with nonzero constant term is nonsingular. -/
theorem isUnit_companionLastColumn (n : ℕ) (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = n + 1) (h0 : p.eval 0 ≠ 0) :
    IsUnit (Matrix.companionLastColumn n p) :=
  isUnit_of_charpoly_eval_zero_ne_zero (Matrix.charpoly_companionLastColumn n p hp hd) h0

/-- The prescribed characteristic polynomial and positive GMRES curve are
equivalent to the existence of a unitary and upper triangular companion
similarity whose coordinate vector satisfies $Ts=h$. -/
theorem gmres_curve_iff_companion (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (b : Fin (n + 1) → ℂ) (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = n + 1)
    (h0 : p.eval 0 ≠ 0) (f : Fin (n + 1) → ℝ) (hf : Antitone f)
    (hpos : 0 < f (Fin.last n)) :
    (A.charpoly = p ∧
      ∀ k : Fin (n + 1), ∃ x : EuclideanSpace ℂ (Fin (n + 1)),
        IsMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 k.val x ∧
        ‖WithLp.toLp 2 b - Matrix.toEuclideanLin A x‖ = f k) ↔
    (∃ W T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ ∧ T.IsUpperTriangular ∧ IsUnit T ∧
      T *ᵥ gmresCompanionCoefficients n p = WithLp.ofLp (gmresCurveCoordinates f) ∧
      b = W *ᵥ WithLp.ofLp (gmresCurveCoordinates f) ∧
      A = W * T * Matrix.companionLastColumn n p * T⁻¹ * Wᴴ) := by
  have hs := companionLastColumn_mul_gmresCompanionCoefficients n p hp hd h0
  constructor
  · rintro ⟨hchar, hx⟩
    choose x hx hr using hx
    exact companion_of_gmres_curve hchar h0 hs f hf hpos x hx hr
  · rintro ⟨W, T, hW, hT, hTu, hTs, hb, hA⟩
    obtain ⟨hchar, hr⟩ := gmres_curve_of_companion hp hd f hf hpos.le hW hT hTu hs hTs hb hA
    refine ⟨hchar, fun k => ?_⟩
    obtain ⟨x, hx⟩ :=
      exists_isMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 k.val
    exact ⟨x, hx, hr k x hx⟩

end Krylov
