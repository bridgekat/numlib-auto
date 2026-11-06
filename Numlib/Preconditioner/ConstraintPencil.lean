/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.SaddlePoint

/-!
# The primal block pencil

For the pencil `(diag(E, 0), [I, Bᴴ; B, -C])`, the equation at zero leaves the multiplier
free. At a nonzero eigenvalue, the lower block equation is `Bx = Cy`, so the denominator
of the eigenvalue's Rayleigh quotient is `xᴴx + yᴴCy`. It is positive when `C` is positive
semidefinite and `Bᴴ` is injective.
-/

open scoped ComplexOrder

namespace Matrix

variable {n m K : Type*} [Fintype n] [Fintype m]

omit [Fintype n] [Fintype m] in
private theorem sumElim_eq_zero_iff [Zero K] {x : n → K} {y : m → K} :
    Sum.elim x y = 0 ↔ x = 0 ∧ y = 0 := by
  have hz : (0 : n ⊕ m → K) = Sum.elim (0 : n → K) (0 : m → K) := by
    funext i
    cases i <;> rfl
  rw [hz, Sum.elim_eq_iff]

section Zero

variable [Field K]

/-- At zero, a primal block pencil has exactly the nonzero pairs `(x,y)` with `E x = 0`.
The second matrix of the pencil is immaterial. -/
theorem hasPencilEigenvector_primalBlock_zero_iff
    (E : Matrix n n K) (P : Matrix (n ⊕ m) (n ⊕ m) K) (x : n → K) (y : m → K) :
    HasPencilEigenvector (fromBlocks E 0 0 0) P 0 (Sum.elim x y) ↔
      Sum.elim x y ≠ 0 ∧ E *ᵥ x = 0 := by
  simp [HasPencilEigenvector, fromBlocks_mulVec_sumElim_eq_zero_iff]

/-- The kernel of `diag(E, 0)` has dimension `nullity(E) + m`. -/
theorem finrank_ker_fromBlocks_primal (E : Matrix n n K) :
    Module.finrank K (LinearMap.ker
      (fromBlocks E 0 0 (0 : Matrix m m K)).mulVecLin) =
      Module.finrank K (LinearMap.ker E.mulVecLin) + Fintype.card m := by
  let P := fromBlocks E 0 0 (0 : Matrix m m K)
  have hker (x : n → K) (y : m → K) :
      Sum.elim x y ∈ LinearMap.ker P.mulVecLin ↔ E *ᵥ x = 0 := by
    simp [P, LinearMap.mem_ker, fromBlocks_mulVec_sumElim_eq_zero_iff]
  let e : LinearMap.ker P.mulVecLin ≃ₗ[K] LinearMap.ker E.mulVecLin × (m → K) :=
    { toFun := fun z ↦
        (⟨z.val ∘ Sum.inl, (hker (z.val ∘ Sum.inl) (z.val ∘ Sum.inr)).mp (by
          rw [Sum.elim_comp_inl_inr]
          exact z.property)⟩, z.val ∘ Sum.inr)
      invFun := fun z ↦ ⟨Sum.elim z.1.val z.2, (hker _ _).mpr z.1.property⟩
      left_inv := fun z ↦ Subtype.ext (Sum.elim_comp_inl_inr z.val)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

end Zero

section Complex

variable [DecidableEq n] {B : Matrix m n ℂ} {C : Matrix m m ℂ} {E : Matrix n n ℂ}
variable {γ : ℂ} {x : n → ℂ} {y : m → ℂ}

private theorem primalBlock_equations
    (h : HasPencilEigenvector (fromBlocks E 0 0 0) (fromBlocks 1 Bᴴ B (-C)) γ
      (Sum.elim x y)) :
    E *ᵥ x = γ • (x + Bᴴ *ᵥ y) ∧ (0 : m → ℂ) = γ • (B *ᵥ x - C *ᵥ y) := by
  rcases h with ⟨_, h⟩
  rw [fromBlocks_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  refine ⟨?_, ?_⟩
  · funext i
    simpa only [Pi.smul_apply, Sum.elim_inl, one_mulVec, zero_mulVec, add_zero] using
      congrFun h (Sum.inl i)
  · funext i
    simpa only [Pi.smul_apply, Sum.elim_inr, zero_mulVec, add_zero, neg_mulVec,
      sub_eq_add_neg] using congrFun h (Sum.inr i)

private theorem primalBlock_nonzero_data (hB : Function.Injective Bᴴ.mulVec)
    (hγ : γ ≠ 0)
    (h : HasPencilEigenvector (fromBlocks E 0 0 0) (fromBlocks 1 Bᴴ B (-C)) γ
      (Sum.elim x y)) :
    x ≠ 0 ∧ B *ᵥ x = C *ᵥ y ∧ E *ᵥ x = γ • (x + Bᴴ *ᵥ y) := by
  obtain ⟨htop, hbot⟩ := primalBlock_equations h
  refine ⟨?_, sub_eq_zero.mp ((smul_eq_zero.mp hbot.symm).resolve_left hγ), htop⟩
  intro hx
  have hy : y = 0 := hB (by
    rw [hx, mulVec_zero, zero_add] at htop
    simpa using (smul_eq_zero.mp htop.symm).resolve_left hγ)
  exact h.1 (sumElim_eq_zero_iff.mpr ⟨hx, hy⟩)

omit [DecidableEq n] in
private theorem star_dotProduct_add_adjoint_mulVec (h : B *ᵥ x = C *ᵥ y) (hC : C.IsHermitian) :
    star x ⬝ᵥ (x + Bᴴ *ᵥ y) = star x ⬝ᵥ x + star y ⬝ᵥ (C *ᵥ y) := by
  rw [dotProduct_add, dotProduct_mulVec, ← star_mulVec, h, star_mulVec, hC.eq,
    ← dotProduct_mulVec]

omit [DecidableEq n] in
private theorem primalBlock_denom_pos (hC : C.PosSemidef) (hx : x ≠ 0) :
    0 < star x ⬝ᵥ x + star y ⬝ᵥ (C *ᵥ y) :=
  add_pos_of_pos_of_nonneg (dotProduct_star_self_pos_iff.mpr hx) (hC.dotProduct_mulVec_nonneg y)

/-- For an eigenpair of the primal block pencil, the eigenvalue is zero exactly when `E x = 0`.
There is no condition on `y` beyond the requirement that the pair be nonzero. -/
theorem HasPencilEigenvector.primalBlock_eq_zero_iff (hB : Function.Injective Bᴴ.mulVec)
    (hC : C.PosSemidef)
    (h : HasPencilEigenvector (fromBlocks E 0 0 0) (fromBlocks 1 Bᴴ B (-C)) γ
      (Sum.elim x y)) :
    γ = 0 ↔ E *ᵥ x = 0 := by
  constructor
  · rintro rfl
    exact (hasPencilEigenvector_primalBlock_zero_iff _ _ _ _ |>.mp h).2
  · intro hEx
    by_contra hγ
    obtain ⟨hx, hBx, htop⟩ := primalBlock_nonzero_data hB hγ h
    have hform := congrArg (star x ⬝ᵥ ·) htop
    rw [hEx, dotProduct_zero, dotProduct_smul, star_dotProduct_add_adjoint_mulVec hBx hC.1,
      smul_eq_mul] at hform
    exact (mul_ne_zero hγ (primalBlock_denom_pos hC hx).ne') hform.symm

/-- With positive definite `C` and `E x ≠ 0`, eliminate the multiplier to recover the
eigenvalue as a generalized Rayleigh quotient. -/
theorem HasPencilEigenvector.primalBlock_eq_rayleigh [DecidableEq m]
    (hB : Function.Injective Bᴴ.mulVec) (hC : C.PosDef)
    (h : HasPencilEigenvector (fromBlocks E 0 0 0) (fromBlocks 1 Bᴴ B (-C)) γ
      (Sum.elim x y)) (hEx : E *ᵥ x ≠ 0) :
    γ = (star x ⬝ᵥ (E *ᵥ x)) /
      (star x ⬝ᵥ ((1 + Bᴴ * C⁻¹ * B) *ᵥ x)) ∧ γ ≠ 0 := by
  have hγ : γ ≠ 0 := fun hz ↦ hEx ((h.primalBlock_eq_zero_iff hB hC.posSemidef).mp hz)
  obtain ⟨hx, hBx, htop⟩ := primalBlock_nonzero_data hB hγ h
  have hy : C⁻¹ *ᵥ (B *ᵥ x) = y := by
    rw [hBx, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hC.isUnit),
      one_mulVec]
  have hD : (1 + Bᴴ * C⁻¹ * B) *ᵥ x = x + Bᴴ *ᵥ y := by
    rw [add_mulVec, one_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hy]
  refine ⟨(eq_div_iff ?_).mpr ?_, hγ⟩
  · rw [hD, star_dotProduct_add_adjoint_mulVec hBx hC.1]
    exact (primalBlock_denom_pos hC.posSemidef hx).ne'
  · rw [hD, htop, dotProduct_smul, smul_eq_mul]

/-- The nonzero eigenvalues of the primal block pencil are real. If the spectrum of the
Hermitian primal block is enclosed by `[a,b]`, the eigenvalues of the pencil are enclosed by
`[min 0 a, max 0 b]`. The denominator can exceed the squared norm of the primal component. -/
theorem HasPencilEigenvector.primalBlock_mem_interval
    (hB : Function.Injective Bᴴ.mulVec) (hC : C.PosSemidef)
    {a b : ℝ} (hbounds : E.toEuclideanLin.IsSymmetricBoundedBy a b) (hγ : γ ≠ 0)
    (h : HasPencilEigenvector (fromBlocks E 0 0 0) (fromBlocks 1 Bᴴ B (-C)) γ
      (Sum.elim x y)) :
    γ ∈ Complex.ofReal '' Set.Icc (min 0 a) (max 0 b) := by
  obtain ⟨hx, hBx, htop⟩ := primalBlock_nonzero_data hB hγ h
  let p := (star x ⬝ᵥ x).re
  let c := (star y ⬝ᵥ (C *ᵥ y)).re
  let q := (star x ⬝ᵥ (E *ᵥ x)).re
  have hp : 0 < p := (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hx)).1
  have hc : 0 ≤ c := hC.re_dotProduct_nonneg y
  have hd : 0 < p + c := add_pos_of_pos_of_nonneg hp hc
  have hE : E.IsHermitian := isSymmetric_toEuclideanLin_iff.mp hbounds.isSymmetric
  have hEform : star x ⬝ᵥ (E *ᵥ x) = (q : ℂ) :=
    Complex.ext rfl (by simpa using hE.im_star_dotProduct_mulVec_self x)
  have hCform : star y ⬝ᵥ (C *ᵥ y) = (c : ℂ) :=
    Complex.ext rfl (by simpa using hC.isHermitian.im_star_dotProduct_mulVec_self y)
  have hXform : star x ⬝ᵥ x = (p : ℂ) :=
    Complex.ext rfl (by simpa using (Complex.pos_iff.mp
      (dotProduct_star_self_pos_iff.mpr hx)).2.symm)
  have hdiv : γ = ((q / (p + c) : ℝ) : ℂ) := by
    have hform := congrArg (star x ⬝ᵥ ·) htop
    rw [dotProduct_smul, star_dotProduct_add_adjoint_mulVec hBx hC.1, smul_eq_mul,
      hEform, hXform, hCform, ← Complex.ofReal_add] at hform
    rw [Complex.ofReal_div]
    exact (eq_div_iff (by exact_mod_cast hd.ne')).mpr hform.symm
  let v : EuclideanSpace ℂ n := WithLp.toLp 2 x
  have hv : ‖v‖ ^ 2 = p := by
    simpa [v, p, ← Complex.ofReal_pow] using (congrArg Complex.re (star_dotProduct_self x)).symm
  have hvE : (inner ℂ (E.toEuclideanLin v) v).re = q := by
    change RCLike.re (inner ℂ (E.toEuclideanLin v) v) = q
    rw [inner_re_symm (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
      ofLp_toEuclideanLin]
    rfl
  have hlo := hbounds.le_re_inner v
  have hhi := hbounds.re_inner_le v
  change a * ‖v‖ ^ 2 ≤ (inner ℂ (E.toEuclideanLin v) v).re at hlo
  change (inner ℂ (E.toEuclideanLin v) v).re ≤ b * ‖v‖ ^ 2 at hhi
  rw [hv, hvE] at hlo hhi
  have hpd : p ≤ p + c := le_add_of_nonneg_right hc
  refine ⟨q / (p + c), ⟨(le_div_iff₀ hd).2 ?_, (div_le_iff₀ hd).2 ?_⟩, hdiv.symm⟩
  · calc
      min 0 a * (p + c) ≤ min 0 a * p := mul_le_mul_of_nonpos_left hpd (min_le_left _ _)
      _ ≤ a * p := mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le
      _ ≤ q := hlo
  · calc
      q ≤ b * p := hhi
      _ ≤ max 0 b * p := mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le
      _ ≤ max 0 b * (p + c) := mul_le_mul_of_nonneg_left hpd (le_max_left _ _)

end Complex

end Matrix
