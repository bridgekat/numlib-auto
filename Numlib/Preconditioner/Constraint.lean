/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Constraint preconditioning with a zero trailing block

For two saddle matrices with common off-diagonal blocks, the left-preconditioned matrix
is the identity plus an operator with primal range in the null space of the constraint.
Compression to that null space gives the nontrivial characteristic-polynomial factor.
-/

open Polynomial

namespace Matrix

variable {n m k K : Type*} [Fintype n] [Fintype m] [Fintype k]
variable [DecidableEq n] [DecidableEq m] [DecidableEq k] [Field K] [StarRing K]

/-- The left-preconditioned matrix for two saddle matrices sharing their constraints. -/
noncomputable def constraintPreconditioned (A G : Matrix n n K) (B : Matrix m n K) :
    Matrix (n ⊕ m) (n ⊕ m) K :=
  (saddleMatrix G Bᴴ 0)⁻¹ * saddleMatrix A Bᴴ 0

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem saddleMatrix_add_primal (A G : Matrix n n K) (B : Matrix m n K) :
    saddleMatrix A Bᴴ 0 = saddleMatrix G Bᴴ 0 + fromBlocks (A - G) 0 0 0 := by
  simp [saddleMatrix, fromBlocks_add, add_comm G (A - G)]

/-- The preconditioned matrix has an identity trailing block and a zero upper-right block.
The remaining two blocks are obtained from the first block column of the inverse preconditioner. -/
theorem constraintPreconditioned_eq_fromBlocks {A G : Matrix n n K} {B : Matrix m n K}
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) :
    constraintPreconditioned A G B =
      fromBlocks (1 + ((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₁₁ * (A - G)) 0
        (((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₂₁ * (A - G)) 1 := by
  rw [constraintPreconditioned, saddleMatrix_add_primal A G B, Matrix.mul_add,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hP)]
  conv_lhs =>
    rw [← fromBlocks_one, ← fromBlocks_toBlocks (saddleMatrix G Bᴴ 0)⁻¹]
  simp only [fromBlocks_multiply, fromBlocks_add, Matrix.mul_zero, add_zero, zero_add]

omit [Fintype m] [DecidableEq n] [DecidableEq m] [DecidableEq k] [StarRing K] in
private theorem mul_eq_zero_of_range_eq_ker {Z : Matrix n k K} {B : Matrix m n K}
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin) : B * Z = 0 := by
  classical
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply', mulVecLin_mul, mulVecLin_zero]
  exact LinearMap.range_le_ker_iff.mp hZ.le

omit [DecidableEq k] in
private theorem nullspace_factor_inv {G : Matrix n n K} {B : Matrix m n K} {Z : Matrix n k K}
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) :
    ∃ U : Matrix k n K, ((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₁₁ = Z * U ∧
      (Zᴴ * G * Z) * U = Zᴴ := by
  let P := saddleMatrix G Bᴴ 0
  let H := (P⁻¹).toBlocks₁₁
  let J := (P⁻¹).toBlocks₂₁
  have hp' : P * P⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP)
  have hp : fromBlocks G Bᴴ B 0 * P⁻¹ = fromBlocks 1 0 0 1 := by
    rw [fromBlocks_one]
    simpa only [P, saddleMatrix, conjTranspose_conjTranspose] using hp'
  rw [← fromBlocks_toBlocks P⁻¹, fromBlocks_multiply, fromBlocks_inj] at hp
  have h₁ : G * H + Bᴴ * J = 1 := hp.1
  have h₂ : B * H = 0 := by simpa [H] using hp.2.2.1
  have hcol (j : n) : ∃ z, Z *ᵥ z = H.col j := by
    have hm : H.col j ∈ LinearMap.ker B.mulVecLin := by
      rw [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_single_one, mulVec_mulVec, h₂, zero_mulVec]
    rwa [← hZ] at hm
  choose u hu using hcol
  let U : Matrix k n K := of (fun i j => u j i)
  have hHU : H = Z * U := by
    ext i j
    exact (congrFun (hu j) i).symm
  have hZB : Zᴴ * Bᴴ = 0 := by rw [← conjTranspose_mul, mul_eq_zero_of_range_eq_ker hZ,
    conjTranspose_zero]
  refine ⟨U, hHU, ?_⟩
  have hh := congrArg (fun M => Zᴴ * M) h₁
  simpa [Matrix.mul_add, ← Matrix.mul_assoc, hZB, hHU] using hh

/-- A nonsingular constraint saddle matrix has a nonsingular compression to a basis of the
null space of its constraint. -/
theorem isUnit_nullspaceCompression {G : Matrix n n K} {B : Matrix m n K} {Z : Matrix n k K}
    (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) : IsUnit (Zᴴ * G * Z) := by
  obtain ⟨L, hL⟩ := vecMul_surjective_iff_exists_left_inverse.mp
    ((mulVec_injective_iff.mp hZi).vecMul_surjective)
  obtain ⟨U, -, hU⟩ := nullspace_factor_inv hZ hP
  refine isUnit_iff_exists_inv.mpr ⟨U * Lᴴ, ?_⟩
  rw [← Matrix.mul_assoc, hU, ← conjTranspose_mul, hL, conjTranspose_one]

private theorem nullspace_factor_inv_eq {G : Matrix n n K} {B : Matrix m n K}
    {Z : Matrix n k K} (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) :
    ((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₁₁ = Z * ((Zᴴ * G * Z)⁻¹ * Zᴴ) := by
  obtain ⟨U, hHU, hU⟩ := nullspace_factor_inv hZ hP
  have hG := isUnit_nullspaceCompression hZi hZ hP
  have hU' : U = (Zᴴ * G * Z)⁻¹ * Zᴴ := by
    calc
      U = (Zᴴ * G * Z)⁻¹ * ((Zᴴ * G * Z) * U) := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hG), Matrix.one_mul]
      _ = (Zᴴ * G * Z)⁻¹ * Zᴴ := congrArg ((Zᴴ * G * Z)⁻¹ * ·) hU
  rw [hHU, hU']

omit [DecidableEq n] in
private theorem nullspace_factor_reduced {A G : Matrix n n K} {Z : Matrix n k K}
    (hG : IsUnit (Zᴴ * G * Z)) :
    1 + ((Zᴴ * G * Z)⁻¹ * Zᴴ) * (A - G) * Z = (Zᴴ * G * Z)⁻¹ * (Zᴴ * A * Z) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  have hg := nonsing_inv_mul (Zᴴ * G * Z) ((isUnit_iff_isUnit_det _).mp hG)
  simp only [Matrix.mul_assoc] at hg
  rw [hg]
  abel

omit [StarRing K] in
private theorem charpoly_one_add {l : Type*} [Fintype l] [DecidableEq l] (M : Matrix l l K) :
    (1 + M).charpoly = M.charpoly.comp (X - 1) := by
  simpa [scalar_apply, diagonal_neg, sub_eq_add_neg, add_comm] using
    (charpoly_sub_scalar M (-1))

omit [StarRing K] in
private theorem charpoly_one_add_rectangular {Z : Matrix n k K} (U : Matrix k n K)
    (hcard : Fintype.card k ≤ Fintype.card n) :
    (1 + Z * U).charpoly =
      (X - 1) ^ (Fintype.card n - Fintype.card k) * (1 + U * Z).charpoly := by
  rw [charpoly_one_add, charpoly_one_add, charpoly_mul_comm_of_le _ _ hcard, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.X_comp]

/-- The characteristic polynomial of the constraint-preconditioned matrix factors into
`(X - 1) ^ (2 * card m)` times the characteristic polynomial of the reduced pencil operator.
The reduced factor may contribute additional roots at 1. -/
theorem charpoly_constraintPreconditioned {A G : Matrix n n K} {B : Matrix m n K}
    {Z : Matrix n k K} (hB : Function.Surjective B.mulVec) (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) :
    (constraintPreconditioned A G B).charpoly =
      (X - 1) ^ (2 * Fintype.card m) * ((Zᴴ * G * Z)⁻¹ * (Zᴴ * A * Z)).charpoly := by
  have hH := nullspace_factor_inv_eq hZi hZ hP
  have hG := isUnit_nullspaceCompression hZi hZ hP
  have hcard : Fintype.card m + Fintype.card k = Fintype.card n := by
    have hd := B.mulVecLin.finrank_range_add_finrank_ker
    rwa [LinearMap.range_eq_top.mpr hB, finrank_top, ← hZ,
      LinearMap.finrank_range_of_inj hZi, Module.finrank_pi, Module.finrank_pi,
      Module.finrank_pi] at hd
  rw [constraintPreconditioned_eq_fromBlocks hP, charpoly_fromBlocks_zero₁₂, charpoly_one, hH,
    Matrix.mul_assoc (Z : Matrix n k K), charpoly_one_add_rectangular _ (by omega),
    nullspace_factor_reduced hG]
  rw [show Fintype.card n - Fintype.card k = Fintype.card m by omega, two_mul, pow_add]
  ac_rfl

/-- The eigenspace at 1 consists of vectors with primal part in the kernel of `A - G`
and arbitrary multiplier part. -/
theorem constraintPreconditioned_mulVec_eq_self_iff {A G : Matrix n n K} {B : Matrix m n K}
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) (x : n → K) (y : m → K) :
    constraintPreconditioned A G B *ᵥ Sum.elim x y = Sum.elim x y ↔ A *ᵥ x = G *ᵥ x := by
  let P := saddleMatrix G Bᴴ 0
  have h : P * P⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP)
  rw [← (mulVec_injective_of_isUnit hP).eq_iff, constraintPreconditioned]
  change P *ᵥ ((P⁻¹ * saddleMatrix A Bᴴ 0) *ᵥ Sum.elim x y) = P *ᵥ Sum.elim x y ↔ _
  rw [mulVec_mulVec, ← Matrix.mul_assoc, h, Matrix.one_mul]
  simp [P, saddleMatrix, fromBlocks_mulVec, Sum.elim_eq_iff]

omit [DecidableEq k] in
/-- At an eigenvalue different from 1, the primal component of the eigenvector is `Z *ᵥ z`
for a vector of the compressed pencil. The multiplier is determined by the lower-left block
of the preconditioned matrix and the eigenvalue. -/
theorem constraintPreconditioned_mulVec_eq_smul_iff {A G : Matrix n n K} {B : Matrix m n K}
    {Z : Matrix n k K} (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) {μ : K} (hμ : μ ≠ 1) (x : n → K) (y : m → K) :
    constraintPreconditioned A G B *ᵥ Sum.elim x y = μ • Sum.elim x y ↔
      ∃ z : k → K, x = Z *ᵥ z ∧ (Zᴴ * A * Z) *ᵥ z = μ • ((Zᴴ * G * Z) *ᵥ z) ∧
        y = (μ - 1)⁻¹ • ((((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₂₁ * (A - G)) *ᵥ x) := by
  classical
  let L := ((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₂₁ * (A - G)
  let S := (Zᴴ * G * Z)⁻¹ * Zᴴ * (A - G)
  let T := 1 + Z * S
  have h₁ : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  have hG := isUnit_nullspaceCompression hZi hZ hP
  have hM : constraintPreconditioned A G B = fromBlocks T 0 L 1 := by
    rw [constraintPreconditioned_eq_fromBlocks hP, nullspace_factor_inv_eq hZi hZ hP,
      Matrix.mul_assoc (Z : Matrix n k K)]
  have hsmul : μ • Sum.elim x y = Sum.elim (μ • x) (μ • y) := by
    funext i
    cases i <;> rfl
  rw [hM, fromBlocks_mulVec, hsmul]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_eq_iff, zero_mulVec, add_zero,
    one_mulVec]
  have hy : L *ᵥ x + y = μ • y ↔ y = (μ - 1)⁻¹ • (L *ᵥ x) := by
    rw [eq_inv_smul_iff₀ h₁, sub_smul, one_smul, eq_comm (a := _ - y), eq_sub_iff_add_eq]
  rw [hy]
  have hTZ : T * Z = Z * ((Zᴴ * G * Z)⁻¹ * (Zᴴ * A * Z)) := by
    rw [← nullspace_factor_reduced (A := A) hG]
    simp [T, S, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  have hZeq (z : k → K) :
      T *ᵥ (Z *ᵥ z) = μ • (Z *ᵥ z) ↔ (Zᴴ * A * Z) *ᵥ z = μ • ((Zᴴ * G * Z) *ᵥ z) := by
    rw [mulVec_mulVec, hTZ, ← mulVec_mulVec, ← mulVec_smul, hZi.eq_iff,
      ← (mulVec_injective_of_isUnit hG).eq_iff, mulVec_mulVec, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG), Matrix.one_mul, mulVec_smul]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : Z *ᵥ (S *ᵥ x) = (μ - 1) • x := by
      have hh : x + Z *ᵥ (S *ᵥ x) = μ • x := by
        simpa only [T, add_mulVec, one_mulVec, ← mulVec_mulVec] using hx
      rw [sub_smul, one_smul, eq_sub_iff_add_eq]
      simpa [add_comm] using hh
    let z := (μ - 1)⁻¹ • (S *ᵥ x)
    have hxz : x = Z *ᵥ z := by
      change x = Z *ᵥ ((μ - 1)⁻¹ • (S *ᵥ x))
      rw [mulVec_smul, hx', eq_inv_smul_iff₀ h₁]
    refine ⟨z, hxz, (hZeq z).mp ?_, hy⟩
    rwa [← hxz]
  · rintro ⟨z, hxz, hz, hy⟩
    exact ⟨hxz ▸ (hZeq z).mpr hz, hy⟩

section Eigenfamilies

open Function Submodule
open scoped ComplexOrder

omit [StarRing K] in
private theorem linearIndependent_sum_of_map_eq_zero {ι ι' V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {v : ι → V} {w : ι' → V} {f : V →ₗ[K] W}
    (hv : LinearIndependent K v) (hv₀ : ∀ i, f (v i) = 0)
    (hw : LinearIndependent K (f ∘ w)) :
    LinearIndependent K (Sum.elim v w) := by
  refine hv.sum_type (LinearIndependent.of_comp f hw) ?_
  apply (Submodule.range_ker_disjoint hw).symm.mono_left
  rintro _ hx
  exact (span_le.mpr (by rintro _ ⟨i, rfl⟩; exact LinearMap.mem_ker.mpr (hv₀ i))) hx

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [StarRing K] in
private theorem linearIndependent_sumElim_zero {ι ι' : Type*} {v : ι → n → K} {w : ι' → m → K}
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K
      (Sum.elim (fun i => Sum.elim (0 : n → K) (w i)) (fun i => Sum.elim (v i) (0 : m → K))) := by
  let p := LinearMap.funLeft K K (Sum.inl : n → n ⊕ m)
  let q := LinearMap.funLeft K K (Sum.inr : m → n ⊕ m)
  refine linearIndependent_sum_of_map_eq_zero (f := p) ?_ (fun _ => rfl) ?_
  · refine LinearIndependent.of_comp q ?_
    change LinearIndependent K w
    exact hw
  · change LinearIndependent K v
    exact hv

omit [StarRing K] in
private theorem linearIndependent_join_one_eigenvectors {ι ι' V : Type*} [AddCommGroup V]
    [Module K V] {T : V →ₗ[K] V} {u : ι → V} {v : ι' → V} {d : ι' → K}
    (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (hTu : ∀ i, T (u i) = u i) (hTv : ∀ j, T (v j) = d j • v j)
    (hd : ∀ j, d j ≠ 1) : LinearIndependent K (Sum.elim u v) := by
  refine linearIndependent_sum_of_map_eq_zero (f := T - LinearMap.id) hu ?_ ?_
  · intro i
    rw [LinearMap.sub_apply, LinearMap.id_apply, hTu, sub_self]
  · convert hv.units_smul (fun j => Units.mk0 (d j - 1) (sub_ne_zero.mpr (hd j))) using 1
    funext j
    simp [hTv, sub_smul]

variable {𝕜 : Type*} [RCLike 𝕜]

omit [DecidableEq k] in
/-- If the reduced preconditioner is positive definite, a basis of its symmetric pencil
supplies one lifted eigenvector for each reduced eigenvalue different from 1, counted with
multiplicity. These lifts, the multiplier coordinate vectors, and the primal vectors
of a basis of the kernel of `A - G` are jointly linearly independent. -/
theorem exists_constraintPreconditioned_eigenvectors {A G : Matrix n n 𝕜} {B : Matrix m n 𝕜}
    {Z : Matrix n k 𝕜} (hA : A.IsHermitian) (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hP : IsUnit (saddleMatrix G Bᴴ 0)) (hG : (Zᴴ * G * Z).PosDef) :
    ∃ (w : Fin (Module.finrank 𝕜 (LinearMap.ker (A - G).mulVecLin)) → n → 𝕜)
      (d : k → ℝ) (z : k → k → 𝕜) (y : {j // d j ≠ 1} → m → 𝕜),
      (∀ i, A *ᵥ w i = G *ᵥ w i) ∧
      (∀ j, HasPencilEigenvector (Zᴴ * A * Z) (Zᴴ * G * Z) (d j : 𝕜) (z j)) ∧
      LinearIndependent 𝕜 z ∧
      let u := Sum.elim (fun j : m => Sum.elim (0 : n → 𝕜) (Pi.single j 1))
        (fun i => Sum.elim (w i) (0 : m → 𝕜))
      let v := fun j : {j // d j ≠ 1} => Sum.elim (Z *ᵥ z j) (y j)
      let M := constraintPreconditioned A G B
      LinearIndependent 𝕜 (Sum.elim u v) ∧ (∀ i, M *ᵥ u i = u i) ∧
        (∀ j, M *ᵥ v j = (d j : 𝕜) • v j) := by
  classical
  let W := LinearMap.ker (A - G).mulVecLin
  let e := Module.finBasis 𝕜 W
  let w := W.subtype ∘ e
  have hw (i) : A *ᵥ w i = G *ᵥ w i := by
    have hh := LinearMap.mem_ker.mp (e i).property
    simpa [w, W, sub_mulVec, sub_eq_zero] using hh
  obtain ⟨F, d, hF, hFG, hFA, -⟩ := exists_simultaneous_diagonalization
    (isHermitian_conjTranspose_mul_mul Z hA) hG
  have hz (j) : HasPencilEigenvector (Zᴴ * A * Z) (Zᴴ * G * Z) (d j : 𝕜) (F.col j) :=
    hasPencilEigenvector_col_of_conj_eq_diagonal hF hFG hFA j
  let J := {j // d j ≠ 1}
  let L := ((saddleMatrix G Bᴴ 0)⁻¹).toBlocks₂₁ * (A - G)
  let y := fun j : J => ((d j : 𝕜) - 1)⁻¹ • (L *ᵥ (Z *ᵥ F.col j))
  let u := Sum.elim (fun j : m => Sum.elim (0 : n → 𝕜) (Pi.single j 1))
    (fun i => Sum.elim (w i) (0 : m → 𝕜))
  let v := fun j : J => Sum.elim (Z *ᵥ F.col j) (y j)
  let M := constraintPreconditioned A G B
  have hFcol := linearIndependent_cols_of_isUnit hF
  refine ⟨w, d, F.col, y, hw, hz, hFcol, ?_⟩
  change LinearIndependent 𝕜 (Sum.elim u v) ∧ (∀ i, M *ᵥ u i = u i) ∧
    (∀ j : J, M *ᵥ v j = (d j : 𝕜) • v j)
  have hMu (i) : M *ᵥ u i = u i := by
    cases i with
    | inl j => exact (constraintPreconditioned_mulVec_eq_self_iff hP _ _).mpr (by simp)
    | inr j => exact (constraintPreconditioned_mulVec_eq_self_iff hP _ _).mpr (hw j)
  have hd (j : J) : (d j : 𝕜) ≠ 1 := by
    intro h
    exact j.property (RCLike.ofReal_injective (h.trans RCLike.ofReal_one.symm))
  have hMv (j : J) : M *ᵥ v j = (d j : 𝕜) • v j :=
    (constraintPreconditioned_mulVec_eq_smul_iff hZi hZ hP (hd j) _ _).mpr
      ⟨F.col j, rfl, (hz j).2, rfl⟩
  refine ⟨?_, hMu, hMv⟩
  have hwi : LinearIndependent 𝕜 w := e.linearIndependent.map' W.subtype W.ker_subtype
  have hPi := Pi.linearIndependent_single_one m 𝕜
  have hui : LinearIndependent 𝕜 u := linearIndependent_sumElim_zero hwi hPi
  have hvi : LinearIndependent 𝕜 v := by
    apply LinearIndependent.of_comp (LinearMap.funLeft 𝕜 𝕜 (Sum.inl : n → n ⊕ m))
    exact (hFcol.comp Subtype.val Subtype.val_injective).map' Z.mulVecLin
      (LinearMap.ker_eq_bot.mpr hZi)
  exact linearIndependent_join_one_eigenvectors (T := M.mulVecLin) hui hvi hMu hMv hd

end Eigenfamilies

end Matrix
