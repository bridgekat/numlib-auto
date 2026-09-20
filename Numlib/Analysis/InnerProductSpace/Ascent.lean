/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Adjoint`, beside `IsSelfAdjoint.isSymmetric`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The ascent of a self-adjoint operator is one

For a self-adjoint bounded operator `A` on a Hilbert space, `A² v = 0` forces
`‖A v‖² = ⟪A² v, v⟫ = 0`, so `ker (A²) = ker A` (`IsSelfAdjoint.ker_sq_eq_ker`), and by induction
`ker (Aᵏ) = ker A` for every `k ≥ 1` (`IsSelfAdjoint.ker_pow_eq_ker`): the ascent of `A` is one.
Applied to `A = T - λ` for a self-adjoint `T` and a real `λ` (`starRingEnd 𝕜 λ = λ`), the
algebraic and geometric multiplicities of an eigenvalue of a self-adjoint operator coincide,
`ker ((T - λ)ᵏ) = ker (T - λ)` (`IsSelfAdjoint.ker_pow_sub_smul_eq_ker`,
`IsSelfAdjoint.ker_sq_sub_smul_eq_ker`); the operator `λ - T` is covered as well
(`IsSelfAdjoint.ker_sq_smul_sub_eq_ker`, `IsSelfAdjoint.ker_pow_smul_sub_eq_ker`).

The induction step is the general `ContinuousLinearMap.ker_pow_eq_ker_of_ker_sq_eq`: an operator
whose kernel stabilizes at the second power has `ker (Aᵏ) = ker A` for every `k ≥ 1`.

## References

* [brezis2011functional] Comments on Chapter 6, 3 (last sentence) and Problem 36.
* [han2009theoretical] Theorem 2.8.15, the index clause.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

section General

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- **An operator whose kernel stabilizes at the second power has `ker (Aᵏ) = ker A` for every
`k ≥ 1`**: from `ker (A²) = ker A`, `Aᵏ⁺¹ x = 0` means `A x ∈ ker (Aᵏ) = ker A`, so
`x ∈ ker (A²) = ker A`. -/
theorem ContinuousLinearMap.ker_pow_eq_ker_of_ker_sq_eq (A : M →L[R] M)
    (h : LinearMap.ker ((A ^ 2 : M →L[R] M) : M →ₗ[R] M) = LinearMap.ker (A : M →ₗ[R] M))
    {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker ((A ^ k : M →L[R] M) : M →ₗ[R] M) = LinearMap.ker (A : M →ₗ[R] M) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_succ, mul_apply_eq_comp] at hx
      have hAx : A x ∈ LinearMap.ker ((A ^ n : M →L[R] M) : M →ₗ[R] M) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        exact hx
      rw [ih hn] at hAx
      have hx2 : x ∈ LinearMap.ker ((A ^ 2 : M →L[R] M) : M →ₗ[R] M) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_two, mul_apply_eq_comp]
        exact hAx
      rwa [h] at hx2
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      rw [pow_succ, mul_apply_eq_comp, hx, map_zero]

end General

namespace IsSelfAdjoint

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **The ascent of a self-adjoint operator is one**: `ker (A²) = ker A`, since `A² v = 0` gives
`‖A v‖² = ⟪A v, A v⟫ = ⟪A² v, v⟫ = 0`. -/
theorem ker_sq_eq_ker {A : H →L[𝕜] H} (hA : IsSelfAdjoint A) :
    LinearMap.ker ((A ^ 2 : H →L[𝕜] H) : H →ₗ[𝕜] H) = LinearMap.ker (A : H →ₗ[𝕜] H) := by
  refine le_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_two, mul_apply_eq_comp] at hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hinner : ⟪A v, A v⟫_𝕜 = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq, hv, inner_zero_left]
    exact inner_self_eq_zero.1 hinner
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [pow_two, mul_apply_eq_comp, hv, map_zero]

/-- `ker (Aᵏ) = ker A` for every `k ≥ 1` and self-adjoint `A`. -/
theorem ker_pow_eq_ker {A : H →L[𝕜] H} (hA : IsSelfAdjoint A) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker ((A ^ k : H →L[𝕜] H) : H →ₗ[𝕜] H) = LinearMap.ker (A : H →ₗ[𝕜] H) :=
  A.ker_pow_eq_ker_of_ker_sq_eq hA.ker_sq_eq_ker hk

/-- `T - λ` is self-adjoint when `T` is and `λ` is real. -/
theorem sub_smul_one {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜} (hl : starRingEnd 𝕜 l = l) :
    IsSelfAdjoint (T - l • (1 : H →L[𝕜] H)) :=
  have hl' : IsSelfAdjoint l := hl
  hT.sub (hl'.smul (IsSelfAdjoint.one (H →L[𝕜] H)))

/-- `λ - T` is self-adjoint when `T` is and `λ` is real. -/
theorem smul_one_sub {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜} (hl : starRingEnd 𝕜 l = l) :
    IsSelfAdjoint (l • (1 : H →L[𝕜] H) - T) :=
  have hl' : IsSelfAdjoint l := hl
  (hl'.smul (IsSelfAdjoint.one (H →L[𝕜] H))).sub hT

/-- **The algebraic and geometric multiplicities of an eigenvalue of a self-adjoint operator
coincide**: `ker ((T - λ)²) = ker (T - λ)` for a self-adjoint `T` and a real `λ`
([brezis2011functional] Comments on Chapter 6, 3; [han2009theoretical] Theorem 2.8.15). -/
theorem ker_sq_sub_smul_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) :
    LinearMap.ker (((T - l • (1 : H →L[𝕜] H)) ^ 2 : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((T - l • (1 : H →L[𝕜] H) : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.sub_smul_one hl).ker_sq_eq_ker

/-- `ker ((T - λ)ᵏ) = ker (T - λ)` for every `k ≥ 1`, a self-adjoint `T` and a real `λ`. -/
theorem ker_pow_sub_smul_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker (((T - l • (1 : H →L[𝕜] H)) ^ k : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((T - l • (1 : H →L[𝕜] H) : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.sub_smul_one hl).ker_pow_eq_ker hk

/-- `ker ((λ - T)²) = ker (λ - T)` for a self-adjoint `T` and a real `λ`. -/
theorem ker_sq_smul_sub_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) :
    LinearMap.ker (((l • (1 : H →L[𝕜] H) - T) ^ 2 : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((l • (1 : H →L[𝕜] H) - T : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.smul_one_sub hl).ker_sq_eq_ker

/-- `ker ((λ - T)ᵏ) = ker (λ - T)` for every `k ≥ 1`, a self-adjoint `T` and a real `λ`. -/
theorem ker_pow_smul_sub_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker (((l • (1 : H →L[𝕜] H) - T) ^ k : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((l • (1 : H →L[𝕜] H) - T : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.smul_one_sub hl).ker_pow_eq_ker hk

end IsSelfAdjoint
