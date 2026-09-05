import Numlib.Surface.SaadSparse.Basic

/-!
# §1.13 Basic concepts in linear systems

Section 1.13 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the three existence cases of §1.13.1, the matrix `p`-norms and the condition number
`κ_p(A) = ‖A‖_p ‖A⁻¹‖_p` of §1.13.2, the relative perturbation bound (1.76) and the
residual–error relation.

The condition number is the backbone's `NormedRing.condNumber` of the operator
`x ↦ A x` on `PiLp p (fun _ : Fin n => 𝕜)`, and the perturbation bounds are
`relative_error_le_condNumber` and `relative_error_le_condNumber_mul_relative_residual`
of `Numlib/LinearSolve/Perturbation.lean`.

The differentiability statement of (1.74)–(1.75) (`ε ↦ (A + εE)⁻¹(b + εe)` is differentiable at
`0`) is left out: it is Mathlib calculus rather than a specialization of the backbone, and the
plan lists it as a candidate for `Numlib/LinearSolve/Perturbation.lean`.  Example 1.5 is likewise
left out (an explicit computation, marked optional in the plan).
-/

open Matrix

open scoped SaadSparse NormedRing ENNReal

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### Existence (§1.13.1) -/

/-- Saad §1.13.1, Case 1: a nonsingular matrix gives a unique solution. -/
theorem existsUnique_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) (hA : IsUnit A) (b : Fin n → 𝕜) :
    ∃! x, A *ᵥ x = b := by
  refine ⟨A⁻¹ *ᵥ b, ?_, fun y hy => ?_⟩
  · change A *ᵥ (A⁻¹ *ᵥ b) = b
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]
  · rw [← hy, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- Saad §1.13.1, Case 2: when `b` is attained, the solution set is the coset `x₀ + Null A`. -/
theorem setOf_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) {b x₀ : Fin n → 𝕜} (hx₀ : A *ᵥ x₀ = b) :
    {x | A *ᵥ x = b} = (fun z => x₀ + z) '' {z | A *ᵥ z = 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x - x₀, by rw [mulVec_sub, hx, hx₀, sub_self], by abel⟩
  · rintro ⟨z, hz, rfl⟩
    rw [mulVec_add, hx₀, hz, add_zero]

/-- Saad §1.13.1, Case 2: a singular matrix with `b ∈ Ran A` gives infinitely many solutions. -/
theorem infinite_setOf_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) (hA : ¬ IsUnit A)
    {b x₀ : Fin n → 𝕜} (hx₀ : A *ᵥ x₀ = b) : {x | A *ᵥ x = b}.Infinite := by
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp (mulVec_injective_iff_isUnit.not.mpr hA)
  have hker : A *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
  have hne0 : u - v ≠ 0 := sub_ne_zero_of_ne hne
  refine Set.infinite_of_injective_forall_mem (f := fun c : 𝕜 => x₀ + c • (u - v)) ?_ ?_
  · intro c d hcd
    have h : (c - d) • (u - v) = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_right_injective x₀ hcd
    rcases smul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne0
  · intro c
    simp only [Set.mem_ofPred_eq, mulVec_add, hx₀, mulVec_smul, hker, smul_zero, add_zero]

/-- Saad §1.13.1, Case 3: no solution when `b ∉ Ran A`. -/
theorem not_exists_mulVec_eq (A : Matrix (Fin n) (Fin n) 𝕜) {b : Fin n → 𝕜}
    (hb : b ∉ Set.range (A *ᵥ ·)) : ¬ ∃ x, A *ᵥ x = b := fun ⟨x, hx⟩ => hb ⟨x, hx⟩

/-! ### Matrix `p`-norms and the condition number (§1.13.2) -/

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The operator `x ↦ A x` on `PiLp p (fun _ : Fin n => 𝕜)`, whose norm is the matrix `p`-norm
`‖A‖_p` induced by the vector `p`-norm. -/
noncomputable def lpCLM (A : Matrix (Fin n) (Fin n) 𝕜) :
    PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
  LinearMap.toContinuousLinearMap (toLpLin p p A)

@[simp]
theorem lpCLM_apply (A : Matrix (Fin n) (Fin n) 𝕜) (x : PiLp p (fun _ : Fin n => 𝕜)) :
    lpCLM p A x = WithLp.toLp p (A *ᵥ WithLp.ofLp x) := rfl

theorem lpCLM_one : lpCLM p (1 : Matrix (Fin n) (Fin n) 𝕜) = 1 := by
  ext x i; simp

theorem lpCLM_mul (A B : Matrix (Fin n) (Fin n) 𝕜) :
    lpCLM p (A * B) = lpCLM p A * lpCLM p B := by
  ext x i; simp [← mulVec_mulVec]

theorem lpCLM_add (A B : Matrix (Fin n) (Fin n) 𝕜) :
    lpCLM p (A + B) = lpCLM p A + lpCLM p B := by
  ext x i; simp [add_mulVec]

theorem lpCLM_smul (c : 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜) :
    lpCLM p (c • A) = c • lpCLM p A := by
  ext x i; simp [smul_mulVec]

/-- Saad §1.13.2: `‖A‖_p`, the matrix norm induced by the vector `p`-norm. -/
noncomputable def lpOpNorm (A : Matrix (Fin n) (Fin n) 𝕜) : ℝ := ‖lpCLM p A‖

@[simp]
theorem lpOpNorm_zero : lpOpNorm p (0 : Matrix (Fin n) (Fin n) 𝕜) = 0 := by
  have h : lpCLM p (0 : Matrix (Fin n) (Fin n) 𝕜) = 0 := by ext x i; simp
  rw [lpOpNorm, h, norm_zero]

/-- Saad §1.13.2: the condition number `κ_p(A) = ‖A‖_p ‖A⁻¹‖_p`. -/
noncomputable def condNumberLp (A : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  lpOpNorm p A * lpOpNorm p A⁻¹

open scoped Matrix.Norms.L2Operator in
/-- For `p = 2` the induced norm is Mathlib's scoped `L2Operator` matrix norm. -/
theorem lpOpNorm_two (A : Matrix (Fin n) (Fin n) 𝕜) : lpOpNorm 2 A = ‖A‖ :=
  (l2_opNorm_def A).symm

/-- `A` invertible as a matrix, as a continuous linear equivalence of `PiLp p`. -/
noncomputable def lpEquiv {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    PiLp p (fun _ : Fin n => 𝕜) ≃L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (toLpLin p p A) (toLpLin p p A⁻¹)
      (by rw [← toLpLin_mul_same, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA),
        toLpLin_one])
      (by rw [← toLpLin_mul_same, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
        toLpLin_one]))

@[simp]
theorem lpEquiv_apply {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A)
    (x : PiLp p (fun _ : Fin n => 𝕜)) : lpEquiv p hA x = WithLp.toLp p (A *ᵥ WithLp.ofLp x) := rfl

@[simp]
theorem lpEquiv_symm_apply {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A)
    (x : PiLp p (fun _ : Fin n => 𝕜)) :
    (lpEquiv p hA).symm x = WithLp.toLp p (A⁻¹ *ᵥ WithLp.ofLp x) := rfl

theorem coe_lpEquiv {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    ((lpEquiv p hA : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜)))
      = lpCLM p A := by
  ext x i; simp

theorem coe_lpEquiv_symm {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    (((lpEquiv p hA).symm : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜)))
      = lpCLM p A⁻¹ := by
  ext x i; simp

/-- The condition number `κ_p(A)` is the backbone's `NormedRing.condNumber` of the operator
`x ↦ A x` on `PiLp p`. -/
theorem condNumberLp_eq_condNumber {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    condNumberLp p A = κ (lpCLM p A) := by
  rw [condNumberLp, lpOpNorm, lpOpNorm, ← coe_lpEquiv p hA, ← coe_lpEquiv_symm p hA,
    ContinuousLinearEquiv.condNumber_eq]

/-! ### Properties of the condition number (§1.13.2) -/

/-- Saad §1.13.2: `κ_p` is invariant under scaling. -/
theorem condNumberLp_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix (Fin n) (Fin n) 𝕜) :
    condNumberLp p (c • A) = condNumberLp p A := by
  by_cases hA : IsUnit A
  · have hcA : IsUnit (c • A) := by
      rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
      exact mul_ne_zero (pow_ne_zero _ hc)
        (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det A).mp hA))
    rw [condNumberLp_eq_condNumber p hcA, condNumberLp_eq_condNumber p hA, lpCLM_smul,
      NormedRing.condNumber_smul hc]
  · have hcA : ¬ IsUnit (c • A) := by
      intro h
      refine hA ?_
      have hAeq : A = c⁻¹ • (c • A) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hAeq, isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc))
        (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp h))
    rw [condNumberLp, condNumberLp, nonsing_inv_apply_not_isUnit _
        (fun h => hcA ((isUnit_iff_isUnit_det _).mpr h)),
      nonsing_inv_apply_not_isUnit _ (fun h => hA ((isUnit_iff_isUnit_det _).mpr h)),
      lpOpNorm_zero, mul_zero, mul_zero]

/-- Saad §1.13.2: `κ_p(A) ≥ 1` for a nonsingular `A`. -/
theorem one_le_condNumberLp [NeZero n] {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    1 ≤ condNumberLp p A := by
  have : Nontrivial (PiLp p (fun _ : Fin n => 𝕜)) := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    infer_instance
  rw [condNumberLp_eq_condNumber p hA]
  exact NormedRing.one_le_condNumber ((coe_lpEquiv p hA) ▸ (lpEquiv p hA).toUnit.isUnit)

/-- Saad §1.13.2: `κ_p(α I) = 1` although `det (α I) = αⁿ`. -/
theorem condNumberLp_smul_one [NeZero n] {c : 𝕜} (hc : c ≠ 0) :
    condNumberLp p (c • (1 : Matrix (Fin n) (Fin n) 𝕜)) = 1 := by
  rw [condNumberLp_smul p hc, condNumberLp, lpOpNorm, lpOpNorm, inv_one, lpCLM_one]
  have : Nontrivial (PiLp p (fun _ : Fin n => 𝕜)) := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    infer_instance
  rw [norm_one, mul_one]

/-- Saad §1.13.2: `det (α I) = αⁿ`, so the determinant is no indication of conditioning. -/
theorem det_smul_one (c : 𝕜) : (c • (1 : Matrix (Fin n) (Fin n) 𝕜)).det = c ^ n := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin]

/-! ### Perturbation bounds -/

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- Saad (1.76): the relative error of the solution of a perturbed system is at most
`κ_p(A)/(1 - ‖A⁻¹‖_p ‖ΔA‖_p)` times the relative perturbation of the data.  Taking
`ΔA = ε E` and `Δb = ε e` gives the book's `ε κ(A)(‖e‖/‖b‖ + ‖E‖/‖A‖) + o(ε)`. -/
theorem relative_error_le_of_perturbed (hA : IsUnit A) (ΔA : Matrix (Fin n) (Fin n) 𝕜)
    {b Δb x y : PiLp p (fun _ : Fin n => 𝕜)}
    (hx : lpCLM p A x = b) (hy : lpCLM p (A + ΔA) y = b + Δb)
    (hsmall : lpOpNorm p A⁻¹ * lpOpNorm p ΔA < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ condNumberLp p A / (1 - lpOpNorm p A⁻¹ * lpOpNorm p ΔA)
      * (lpOpNorm p ΔA / lpOpNorm p A + ‖Δb‖ / ‖b‖) := by
  have hsym : ‖((lpEquiv p hA).symm : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜]
      PiLp p (fun _ : Fin n => 𝕜))‖ = lpOpNorm p A⁻¹ := by
    rw [coe_lpEquiv_symm]
    rfl
  have h := relative_error_le_condNumber (lpEquiv p hA) (lpCLM p ΔA) (b := b) (Δb := Δb)
    (x := x) (y := y) (by rw [← hx]; rfl) (by rw [← hy, lpCLM_add]; rfl)
    (by rw [hsym]; exact hsmall) hx0 hb
  rw [hsym, coe_lpEquiv p hA] at h
  rw [condNumberLp_eq_condNumber p hA]
  exact h

/-- Saad §1.13.2: `‖x - x̃‖/‖x‖ ≤ κ(A) ‖r‖/‖b‖` with `r = b - A x̃` the residual. -/
theorem relative_error_le_condNumberLp (hA : IsUnit A) {b x : Fin n → 𝕜} (hx : A *ᵥ x = b)
    (hb : (WithLp.toLp p b : PiLp p (fun _ : Fin n => 𝕜)) ≠ 0) (y : Fin n → 𝕜) :
    ‖(WithLp.toLp p (x - y) : PiLp p (fun _ : Fin n => 𝕜))‖ / ‖(WithLp.toLp p x :
        PiLp p (fun _ : Fin n => 𝕜))‖ ≤
      condNumberLp p A *
        (‖(WithLp.toLp p (b - A *ᵥ y) : PiLp p (fun _ : Fin n => 𝕜))‖ /
          ‖(WithLp.toLp p b : PiLp p (fun _ : Fin n => 𝕜))‖) := by
  have hAx : lpEquiv p hA (WithLp.toLp p x) = WithLp.toLp p b := by
    rw [lpEquiv_apply]; congr 1
  have h := relative_error_le_condNumber_mul_relative_residual (lpEquiv p hA) hAx hb
    (y := WithLp.toLp p y)
  rw [condNumberLp_eq_condNumber p hA, ← coe_lpEquiv p hA]
  exact h

end Lp

end Matrix
