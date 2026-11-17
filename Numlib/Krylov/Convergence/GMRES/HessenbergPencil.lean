/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRES.ResidualPolynomial
import Numlib.Eigen.Pencil
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The GMRES Hessenberg pencil

The matrix of the compression of $A^{-1}$ to $A\mathcal K_n$ in the image of the Arnoldi
basis is $G^{-1}H^*$, where $G=\underline H^*\underline H$ is the Gram matrix of the mapped
basis. The reverse characteristic polynomial of this matrix is the determinant of the
pencil $(G,H^*)$ divided by $\det G$.
-/

open Polynomial Matrix Krylov
open scoped ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "ℒ(" A ")" => LinearEquiv.toLinearMap A

variable [FiniteDimensional 𝕜 E]

namespace Arnoldi

private noncomputable def mappedArnoldiBasis (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) :
    Module.Basis (Fin n) 𝕜 ((subspace (ℒ(A)) r n).map (ℒ(A))) :=
  (orthonormalBasis (ℒ(A)) r hn).toBasis.map
    (Submodule.equivMapOfInjective (ℒ(A)) A.injective (subspace (ℒ(A)) r n))

private theorem coe_mappedArnoldiBasis (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) (i : Fin n) :
    (mappedArnoldiBasis A r hn i : E) = A (vec (ℒ(A)) r i) := by
  rw [mappedArnoldiBasis, Module.Basis.map_apply, Submodule.coe_equivMapOfInjective_apply]
  exact congrArg A (coe_orthonormalBasis_apply (ℒ(A)) r hn i)

private theorem gram_mappedArnoldiBasis (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) :
    gram 𝕜 (mappedArnoldiBasis A r hn) =
      (hessenberg (ℒ(A)) r n)ᴴ * hessenberg (ℒ(A)) r n := by
  ext i j
  rw [gram_apply]
  change inner 𝕜 (mappedArnoldiBasis A r hn i : E) (mappedArnoldiBasis A r hn j : E) = _
  rw [coe_mappedArnoldiBasis, coe_mappedArnoldiBasis]
  have h := apply_vec_of_le (ℒ(A)) r (j := j.val) (n := n + 1) (by omega)
  rw [← Fin.sum_univ_eq_sum_range (fun k => coeff (ℒ(A)) r k j.val • vec (ℒ(A)) r k)] at h
  change A (vec (ℒ(A)) r j.val) = _ at h
  rw [h, inner_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, conjTranspose_apply]
  change coeff (ℒ(A)) r k j.val * inner 𝕜 (A (vec (ℒ(A)) r i.val)) (vec (ℒ(A)) r k) =
    star (coeff (ℒ(A)) r k i.val) * coeff (ℒ(A)) r k j.val
  rw [← inner_conj_symm (A (vec (ℒ(A)) r i.val)) (vec (ℒ(A)) r k), mul_comm]
  rfl

/-- Up to the grade, the Gram matrix $\underline H_n^*\underline H_n$ of the image Arnoldi
basis is nonsingular for an invertible operator $A$. -/
theorem isUnit_hessenberg_gram (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) :
    IsUnit ((hessenberg (ℒ(A)) r n)ᴴ * hessenberg (ℒ(A)) r n) := by
  rw [← gram_mappedArnoldiBasis A r hn]
  exact (posDef_gram_of_linearIndependent (mappedArnoldiBasis A r hn).linearIndependent).isUnit

private theorem inverseCompression_toMatrix (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) :
    let W := (subspace (ℒ(A)) r n).map (ℒ(A))
    let H := hessenberg (ℒ(A)) r n
    let B := mappedArnoldiBasis A r hn
    LinearMap.toMatrix B B (compression (ℒ(A.symm)) W) =
      (Hᴴ * H)⁻¹ * (hessenbergSq (ℒ(A)) r n)ᴴ := by
  let W := (subspace (ℒ(A)) r n).map (ℒ(A))
  let H := hessenberg (ℒ(A)) r n
  let B := mappedArnoldiBasis A r hn
  let D := compression (ℒ(A.symm)) W
  let T := LinearMap.toMatrix B B D
  let G := Hᴴ * H
  let C₀ := (hessenbergSq (ℒ(A)) r n)ᴴ
  change T = G⁻¹ * C₀
  have hu : IsUnit G.det := (isUnit_iff_isUnit_det G).1 (isUnit_hessenberg_gram A r hn)
  have hG : G = gram 𝕜 B := (gram_mappedArnoldiBasis A r hn).symm
  have hGT : G * T = C₀ := by
    rw [hG]
    ext i j
    rw [Matrix.mul_apply]
    calc
      _ = ∑ k : Fin n, inner 𝕜 (B i) (B.repr (D (B j)) k • B k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [gram_apply, show T k j = B.repr (D (B j)) k from
          LinearMap.toMatrix_apply B B D k j, inner_smul_right, mul_comm]
      _ = C₀ i j := by
        rw [← inner_sum, Module.Basis.sum_repr]
        change inner 𝕜 (B i) (compression (ℒ(A.symm)) W (B j)) = _
        rw [compression.inner_apply']
        change inner 𝕜 (mappedArnoldiBasis A r hn i : E) (A.symm
          (mappedArnoldiBasis A r hn j : E)) = _
        rw [coe_mappedArnoldiBasis, coe_mappedArnoldiBasis, A.symm_apply_apply,
          ← inner_conj_symm]
        rfl
  rw [← hGT, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]

/-- For invertible $A$ and a GMRES iterate $x_n$ through the grade of $r_0=b-Ax_0$,
write $H_n$ and $\underline H_n$ for the square and rectangular Arnoldi matrices and
let $\beta=\|r_0\|$. In the Arnoldi basis, the correction $x_n-x_0$ has coefficient vector
$(\underline H_n^*\underline H_n)^{-1}H_n^*\beta e_1$. -/
theorem eq_arnoldi_normal_equations {A : E ≃ₗ[𝕜] E} {b x₀ x : E} {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) (b - A x₀)) (hx : IsMinResidualIterate (ℒ(A)) b x₀ n x) :
    let r := b - A x₀
    let H := hessenberg (ℒ(A)) r n
    let G := Hᴴ * H
    let y := G⁻¹ *ᵥ ((hessenbergSq (ℒ(A)) r n)ᴴ *ᵥ firstVec (‖r‖ : 𝕜) n)
    x = x₀ + ∑ j : Fin n, y j • vec (ℒ(A)) r j.val := by
  let r := b - A x₀
  let H := hessenberg (ℒ(A)) r n
  let H₀ := hessenbergSq (ℒ(A)) r n
  let G := Hᴴ * H
  let β : 𝕜 := (‖r‖ : ℝ)
  let v (j : ℕ) := vec (ℒ(A)) r j
  let f := H₀ᴴ *ᵥ firstVec β n
  let y := G⁻¹ *ᵥ f
  change x = x₀ + ∑ j : Fin n, y j • v j.val
  obtain ⟨t, ht⟩ := (mem_subspace_iff_exists_coeffs (ℒ(A)) r n (x - x₀)).1 hx.mem
  change x - x₀ = ∑ j : Fin n, t j • v j.val at ht
  have hAv (i : Fin n) : A (v i.val) ∈ (subspace (ℒ(A)) r n).map (ℒ(A)) :=
    Submodule.mem_map_of_mem (vec_mem_subspace_of_lt (ℒ(A)) r i.isLt)
  have hre : b - A x = r - ∑ j : Fin n, t j • A (v j.val) := by
    have hh := congrArg A ht
    rw [map_sub, map_sum] at hh
    simp_rw [map_smul] at hh
    dsimp only [r]
    rw [← hh]
    abel
  have hg (i j : Fin n) : G i j = inner 𝕜 (A (v i.val)) (A (v j.val)) := by
    change ((hessenberg (ℒ(A)) r n)ᴴ * hessenberg (ℒ(A)) r n) i j = _
    rw [← gram_mappedArnoldiBasis A r hn, gram_apply]
    change inner 𝕜 (mappedArnoldiBasis A r hn i : E) (mappedArnoldiBasis A r hn j : E) = _
    rw [coe_mappedArnoldiBasis, coe_mappedArnoldiBasis]
  have hright (i : Fin n) : inner 𝕜 (A (v i.val)) r = f i := by
    let zero : Fin n := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
    have hv : β • v 0 = r := smul_vec_zero (ℒ(A)) r
    calc
      _ = inner 𝕜 (A (v i.val)) (β • v 0) := congrArg (inner 𝕜 (A (v i.val))) hv.symm
      _ = f i := by
        rw [inner_smul_right, ← inner_conj_symm (A (v i.val)) (v 0)]
        change β * star (coeff (ℒ(A)) r 0 i.val) = (H₀ᴴ *ᵥ firstVec β n) i
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single zero]
        · change β * star (coeff (ℒ(A)) r 0 i.val) =
            star (coeff (ℒ(A)) r 0 i.val) * (if (0 : ℕ) = 0 then β else 0)
          rw [ite_eq_left rfl, mul_comm]
        · intro j _ hj
          have hj0 : j.val ≠ 0 := fun hz => hj (Fin.ext hz)
          simp [firstVec, hj0]
        · simp
  have hnormal : G *ᵥ t = f := by
    funext i
    have h := (Submodule.mem_orthogonal _ _).1 hx.residual_mem_orthogonal _ (hAv i)
    change inner 𝕜 (A (v i.val)) (b - A x) = 0 at h
    rw [hre, inner_sub_right, inner_sum, sub_eq_zero] at h
    simp_rw [inner_smul_right, ← hg] at h
    rw [← hright i, h, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hu : IsUnit G := isUnit_hessenberg_gram A r hn
  have hty : t = y := Matrix.mulVec_injective_iff_isUnit.2 hu
    (hnormal.trans (Matrix.mulVec_nonsing_inv_mulVec hu f).symm)
  rw [hty] at ht
  exact sub_eq_iff_eq_add'.mp ht

end Arnoldi

namespace Krylov

open _root_.Arnoldi

private theorem charpolyRev_inv_mul_eq_pencil {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    {G : Matrix (Fin n) (Fin n) 𝕜} (hG : IsUnit G.det) (C₀ : Matrix (Fin n) (Fin n) 𝕜) :
    (G⁻¹ * C₀).charpolyRev = C G.det⁻¹ * pencilPoly G C₀ := by
  have hm : G.map (C : 𝕜 →+* 𝕜[X]) * (1 - (X : 𝕜[X]) • (G⁻¹ * C₀).map C) =
      G.map C - (X : 𝕜[X]) • C₀.map C := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.map_mul (f := C),
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hd
  change C G.det * (G⁻¹ * C₀).charpolyRev = pencilPoly G C₀ at hd
  rw [← hd, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (isUnit_iff_ne_zero.1 hG), map_one, one_mul]

/-- Up to the grade, the reverse characteristic polynomial of the inverse compression
is the characteristic polynomial of the Arnoldi pencil
$(\underline H_n^*\underline H_n,H_n^*)$ divided by $\det(\underline H_n^*\underline H_n)$. -/
theorem inverseCompressionResidualPoly_eq_normalized_hessenbergPencil
    (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ} (hn : n ≤ grade (ℒ(A)) r) :
    let H := hessenberg (ℒ(A)) r n
    let G := Hᴴ * H
    inverseCompressionResidualPoly A r n =
      C G.det⁻¹ * pencilPoly G (hessenbergSq (ℒ(A)) r n)ᴴ := by
  let W := (subspace (ℒ(A)) r n).map (ℒ(A))
  let B := mappedArnoldiBasis A r hn
  let D := compression (ℒ(A.symm)) W
  let H := hessenberg (ℒ(A)) r n
  let G := Hᴴ * H
  have hG : IsUnit G.det := (isUnit_iff_isUnit_det G).1 (isUnit_hessenberg_gram A r hn)
  change D.charpoly.reverse = _
  rw [← LinearMap.charpoly_toMatrix D B, reverse_charpoly, inverseCompression_toMatrix A r hn]
  exact charpolyRev_inv_mul_eq_pencil hG _

end Krylov
