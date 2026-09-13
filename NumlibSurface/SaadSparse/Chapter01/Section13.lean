import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Conditioning.LinearSystem
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.SaadSparse.Chapter01.Basics

/-!
# Saad §1.13: basic concepts in linear systems

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §1.13: the three existence cases of §1.13.1, the condition number
`κ_p(A) = ‖A‖_p ‖A⁻¹‖_p` of §1.13.2, the first-order perturbation theory (1.74)–(1.75), the relative
perturbation bound (1.76), the residual–error relation, and Example 1.5.

The matrix `p`-norm `‖A‖_p` of (1.7) and the condition number `κ_p(A)` are the backbone's
`Matrix.lpOpNorm` and `Matrix.condNumberLp` of `Numlib/Analysis/Matrix/OperatorNorm`, together
with the scaling invariance `Matrix.condNumberLp_smul`, the bound `Matrix.one_le_condNumberLp` and
`Matrix.condNumberLp_smul_one` (`κ_p(α I) = 1`) of §1.13.2; this file states the book's
perturbation bounds on them.

The condition number is the backbone's `NormedRing.condNumber` of the operator
`x ↦ A x` on `PiLp p (fun _ : Fin n => 𝕜)` (`Matrix.condNumberLp_eq_condNumber`), and the
perturbation bounds are `relative_error_le_condNumber`,
`relative_error_le_condNumber_mul_relative_residual` and `hasDerivAt_perturbed_solution` of
`Numlib/Conditioning/LinearSystem.lean`.  The bridge that carries the last of these to matrices is
`Matrix.ringInverse_lpCLM`: the matrix inverse and the ring inverse of the induced operator agree,
junk values and all, because `Matrix.lpCLM` reflects invertibility (`Matrix.isUnit_lpCLM_iff`).

Example 1.5 is stated with Saad's `‖·‖_∞`, the maximum absolute row sum, which is Mathlib's
scoped `Matrix.Norms.Operator` instance rather than `Matrix.lpOpNorm ⊤`: `PiLp ⊤` carries no
`Fact (1 ≤ ⊤)` instance in Mathlib, and the `Matrix.Norms.Operator` norm is the one the rest of
the §1.5 surface uses for `‖·‖_∞` anyway.
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
  · exact mulVec_nonsing_inv_mulVec hA b
  · exact (nonsing_inv_mulVec_eq hA hy).symm

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

/-! ### The condition number (§1.13.2) -/

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Saad §1.13.2: `det (α I) = αⁿ` while `κ_p(α I) = 1` (`Matrix.condNumberLp_smul_one`), so the
determinant is no indication of conditioning. -/
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
  rw [condNumberLp_eq_condNumber p A]
  exact h

/-- **Saad (1.74)–(1.75)**: the solution `x(ε) = (A + ε E)⁻¹ (b + ε e)` of a linearly perturbed
system is differentiable in `ε` at `0`, with derivative `A⁻¹ (e - E x)` at the unperturbed
solution `x = A⁻¹ b`.  `hasDerivAt_perturbed_solution` of `Numlib/Conditioning/LinearSystem.lean`,
transported to matrices by `Matrix.ringInverse_lpCLM`: the matrix inverse of `A + ε E` is the ring
inverse of the induced operator, junk values included, and `A` invertible makes `A + ε E`
invertible for all small `ε`, so near `0` the function differentiated really is the solution.

Combined with the norm bound `Matrix.relative_error_le_of_perturbed`, this is the first-order form
(1.76) that the book reads off it, `‖x(ε) - x‖/‖x‖ ≤ ε κ(A) (‖E‖/‖A‖ + ‖e‖/‖b‖) + o(ε)`. -/
theorem equation_1_75 (hA : IsUnit A) (E : Matrix (Fin n) (Fin n) 𝕜)
    (b e : PiLp p (fun _ : Fin n => 𝕜)) :
    HasDerivAt (fun ε : 𝕜 => lpCLM p ((A + ε • E)⁻¹) (b + ε • e))
      (lpCLM p A⁻¹ (e - lpCLM p E (lpCLM p A⁻¹ b))) 0 := by
  have h := hasDerivAt_perturbed_solution (lpEquiv p hA) (lpCLM p E) b e
  simpa only [coe_lpEquiv p hA, coe_lpEquiv_symm p hA, ← lpCLM_smul, ← lpCLM_add,
    ringInverse_lpCLM] using h

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
  rw [condNumberLp_eq_condNumber p A, ← coe_lpEquiv p hA]
  exact h

end Lp

/-! ### Example 1.5 -/

section Example

variable {i j : Fin n}

/-- A square-zero perturbation of the identity is inverted by the first two terms of its Neumann
series. -/
private theorem inv_one_add_of_mul_self_eq_zero {T : Matrix (Fin n) (Fin n) 𝕜} (hT : T * T = 0) :
    (1 + T)⁻¹ = 1 - T := by
  refine inv_eq_right_inv ?_
  have h : (1 + T) * (1 - T) = 1 - T * T := by noncomm_ring
  rw [h, hT, sub_zero]

/-- The rank-one matrix `e_i e_jᵀ` of Example 1.5 is square-zero when `i ≠ j`. -/
private theorem single_mul_self_eq_zero (hij : i ≠ j) :
    (single i j (1 : 𝕜) : Matrix (Fin n) (Fin n) 𝕜) * single i j 1 = 0 := by
  ext a b
  simp only [mul_apply, single_apply, zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : j = l
  · subst hl; simp [hij]
  · simp [hl]

open scoped Matrix.Norms.Operator in
/-- The `∞`-norm of `I + α e_i e_jᵀ` is `1 + |α|`: row `i` has the two entries `1` and `α` and
every other row has the single entry `1`. -/
private theorem linfty_opNorm_one_add_smul_single (hij : i ≠ j) (α : 𝕜) :
    ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜)‖ = 1 + ‖α‖ := by
  have hii : (1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) i i = 1 := by
    simp [hij.symm]
  have hij' : (1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) i j = α := by
    simp [hij]
  have hrowi : (∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) i l‖₊) = 1 + ‖α‖₊ := by
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n))) fun l _ hl => ?_,
      Finset.sum_pair hij, hii, hij']
    · simp
    · have hli : i ≠ l := fun h => hl (by simp [← h])
      have hlj : j ≠ l := fun h => hl (by simp [← h])
      simp [hli, hlj]
  have hrowk : ∀ k, k ≠ i →
      (∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) k l‖₊) = 1 := by
    intro k hk
    rw [Finset.sum_eq_single k (fun l _ hl => ?_) fun h => absurd (Finset.mem_univ k) h]
    · simp [Ne.symm hk]
    · simp [Ne.symm hl, Ne.symm hk]
  have hsup : (Finset.univ.sup fun k =>
      ∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) k l‖₊) = 1 + ‖α‖₊ := by
    refine le_antisymm (Finset.sup_le fun k _ => ?_) ?_
    · by_cases hk : k = i
      · subst hk; exact hrowi.le
      · rw [hrowk k hk]; exact le_self_add
    · rw [← hrowi]
      exact Finset.le_sup
        (f := fun k => ∑ l, ‖(1 + α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) k l‖₊)
        (Finset.mem_univ i)
  rw [linfty_opNorm_def, hsup]
  simp

open scoped Matrix.Norms.Operator in
/-- **Saad Example 1.5**: for `A = I + α e_i e_jᵀ` with `i ≠ j`, the inverse is
`A⁻¹ = I - α e_i e_jᵀ` and `κ_∞(A) = (1 + |α|)²`, so the condition number grows without bound
although `det A = 1`.  The book takes `i` the first index and `j` the last; nothing depends on
that beyond `i ≠ j`.

The norm here is Saad's `‖·‖_∞`, the maximum absolute row sum, which is Mathlib's scoped
`Matrix.Norms.Operator` instance — the same norm the rest of §1.5 uses.  The inverse is the first
two terms of the Neumann series, exact because `(e_i e_jᵀ)² = 0`. -/
theorem example_1_5 (hij : i ≠ j) (α : 𝕜) {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A = 1 + α • single i j 1) :
    A⁻¹ = 1 - α • single i j 1 ∧ ‖A‖ = 1 + ‖α‖ ∧ ‖A⁻¹‖ = 1 + ‖α‖ ∧
      ‖A‖ * ‖A⁻¹‖ = (1 + ‖α‖) ^ 2 := by
  have hSS : (α • single i j 1 : Matrix (Fin n) (Fin n) 𝕜) * (α • single i j 1) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, single_mul_self_eq_zero hij, smul_zero, smul_zero]
  have hinv : A⁻¹ = 1 - α • single i j 1 := by
    rw [hA]; exact inv_one_add_of_mul_self_eq_zero hSS
  have h1 : ‖A‖ = 1 + ‖α‖ := by rw [hA]; exact linfty_opNorm_one_add_smul_single hij α
  have h2 : ‖A⁻¹‖ = 1 + ‖α‖ := by
    rw [hinv, show (1 : Matrix (Fin n) (Fin n) 𝕜) - α • single i j 1
        = 1 + (-α) • single i j 1 by rw [neg_smul, ← sub_eq_add_neg],
      linfty_opNorm_one_add_smul_single hij (-α), norm_neg]
  exact ⟨hinv, h1, h2, by rw [h1, h2]; ring⟩

end Example

end Matrix
