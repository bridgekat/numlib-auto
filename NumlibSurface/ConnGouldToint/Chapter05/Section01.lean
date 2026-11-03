import Numlib.Krylov.Preconditioned
import Numlib.Krylov.Singular
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Conjugate gradients

Section 5.1 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter05

open Krylov
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic objective (5.1.1) with linear term `c` and Hessian `H`. -/
noncomputable abbrev quadraticObjective (c : E) (H : E →L[ℝ] E) : E → ℝ :=
  Subproblem.quadModel c H

/-- One pass of the conjugate-direction recurrence (5.1.23)–(5.1.26).
The state contains only the residual and the direction. -/
noncomputable def conjugateDirectionStep (H : E →ₗ[ℝ] E) (state : E × E) : E × E :=
  let Hp := H state.2
  let α := ‖state.1‖ ^ 2 / ⟪state.2, Hp⟫
  let r' := state.1 + α • Hp
  let β := ‖r'‖ ^ 2 / ‖state.1‖ ^ 2
  (r', -r' + β • state.2)

/-- Algorithm 5.1.1 generates conjugate directions from an arbitrary
initial residual, without computing the iterates of Algorithm 5.1.2. -/
noncomputable def algorithm_5_1_1 (H : E →ₗ[ℝ] E) (r₀ : E) (k : ℕ) : E × E :=
  (conjugateDirectionStep H)^[k] (r₀, -r₀)

/-- Algorithm 5.1.1 starts from the prescribed residual and its negative. -/
theorem algorithm_5_1_1_zero (H : E →ₗ[ℝ] E) (r₀ : E) :
    algorithm_5_1_1 H r₀ 0 = (r₀, -r₀) := rfl

/-- The state satisfies the four recurrences (5.1.23)–(5.1.26).
Lean uses total division, so a valid numerical step also requires both
displayed denominators to be nonzero. -/
theorem algorithm_5_1_1_succ (H : E →ₗ[ℝ] E) (r₀ : E) (k : ℕ) :
    let current := algorithm_5_1_1 H r₀ k
    let α := ‖current.1‖ ^ 2 / ⟪current.2, H current.2⟫
    let r' := current.1 + α • H current.2
    let β := ‖r'‖ ^ 2 / ‖current.1‖ ^ 2
    algorithm_5_1_1 H r₀ (k + 1) = (r', -r' + β • current.2) :=
  Function.iterate_succ_apply' _ _ _

private theorem conjugateDirectionStep_eq_CG_step (H : E →ₗ[ℝ] E) (state : CG.State E) :
    conjugateDirectionStep H (-state.r, state.p) = (-(CG.step H state).r, (CG.step H state).p) := by
  let α : ℝ := ‖-state.r‖ ^ 2 / ⟪state.p, H state.p⟫
  let r' := -state.r + α • H state.p
  let β : ℝ := ‖r'‖ ^ 2 / ‖-state.r‖ ^ 2
  have hα : CG.alpha H state = α := by
    rw [CG.alpha, real_inner_self_eq_norm_sq, ← real_inner_comm (H state.p) state.p]
    simp only [α, norm_neg]
  have hr : -(CG.step H state).r = r' := by
    rw [CG.step_r, hα, neg_sub, sub_eq_add_neg, add_comm]
  have hβ : CG.beta H state = β := by
    rw [CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    simp only [β, ← hr, norm_neg]
  change (r', -r' + β • state.p) = (-(CG.step H state).r, (CG.step H state).p)
  rw [CG.step_p, hβ, ← hr, neg_neg]

/-- Algorithm 5.1.1 agrees with the residual and direction in the backbone
CG iteration. The backbone residual uses the opposite sign. -/
theorem algorithm_5_1_1_eq_projectedCG (H : E →ₗ[ℝ] E) (r₀ : E) (k : ℕ) :
    algorithm_5_1_1 H r₀ k =
      (-(CG.iterate H (-r₀) 0 k).r, (CG.iterate H (-r₀) 0 k).p) := by
  induction k with
  | zero => simp [algorithm_5_1_1_zero]
  | succ k ih =>
    change (conjugateDirectionStep H)^[k + 1] (r₀, -r₀) = _
    rw [Function.iterate_succ_apply', ← algorithm_5_1_1, ih, CG.iterate_succ]
    exact conjugateDirectionStep_eq_CG_step _ _

/-- The two division operations of Algorithm 5.1.1 are defined in ordinary
arithmetic when the residual is nonzero and the direction has nonzero curvature. -/
def ConjugateDirectionStepDefined (H : E →ₗ[ℝ] E) (state : E × E) : Prop :=
  state.1 ≠ 0 ∧ ⟪state.2, H state.2⟫ ≠ 0

/-- The step condition is equivalent to nonvanishing of the two denominators
in (5.1.23) and (5.1.25). -/
theorem conjugateDirectionStepDefined_iff (H : E →ₗ[ℝ] E) (state : E × E) :
    ConjugateDirectionStepDefined H state ↔
      ⟪state.2, H state.2⟫ ≠ 0 ∧ ‖state.1‖ ^ 2 ≠ 0 := by
  rw [ConjugateDirectionStepDefined, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff, and_comm]

/-- For a symmetric coercive Hessian, distinct directions produced by
Algorithm 5.1.1 are conjugate. -/
theorem algorithm_5_1_1_conjugate {H : E →ₗ[ℝ] E} (hH : H.IsSymmetricCoercive)
    (r₀ : E) {i j : ℕ} (hij : i ≠ j) :
    ⟪(algorithm_5_1_1 H r₀ i).2, H (algorithm_5_1_1 H r₀ j).2⟫ = 0 := by
  rw [algorithm_5_1_1_eq_projectedCG, algorithm_5_1_1_eq_projectedCG, real_inner_comm]
  exact CG.inner_apply_direction_eq_zero (-r₀) 0 hH hij.symm

/-- For a symmetric coercive Hessian, Algorithm 5.1.1 has a defined next
step whenever its residual is nonzero. -/
theorem algorithm_5_1_1_stepDefined_iff {H : E →ₗ[ℝ] E} (hH : H.IsSymmetricCoercive)
    (r₀ : E) (k : ℕ) :
    ConjugateDirectionStepDefined H (algorithm_5_1_1 H r₀ k) ↔
      (algorithm_5_1_1 H r₀ k).1 ≠ 0 := by
  refine ⟨fun h ↦ h.1, fun hr ↦ ⟨hr, ?_⟩⟩
  rw [algorithm_5_1_1_eq_projectedCG] at hr ⊢
  have hr' : (CG.iterate H (-r₀) 0 k).r ≠ 0 := by simpa only [Prod.fst, neg_ne_zero] using hr
  have hpos := CG.re_inner_apply_direction_pos (-r₀) 0 hH hr'
  rw [real_inner_comm]
  exact ne_of_gt hpos

/-- Algorithm 5.1.2. The state of the conjugate gradient recurrence. The library
stores the residual `-gₖ` in place of the gradient `gₖ`. -/
noncomputable abbrev algorithm_5_1_2 (H : E →ₗ[ℝ] E) (c x₀ : E) (k : ℕ) : CG.State E :=
  CG.iterate H (-c) x₀ k

/-- Algorithm 5.1.3 applies ordinary CG to the congruence-transformed
quadratic. The inverse transformation is `S = R⁻¹`, so the transformed
Hessian and linear term are `S.adjoint ∘ H ∘ S` and `S.adjoint c`. -/
noncomputable abbrev algorithm_5_1_3 {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (c : E) (xbar₀ : F) (k : ℕ) : CG.State F :=
  let S := R.symm.toContinuousLinearMap
  algorithm_5_1_2 (S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap) (S.adjoint c) xbar₀ k

/-- The transformed CG residual stores the negative of the initial gradient. -/
theorem algorithm_5_1_3_zero {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (c : E) (xbar₀ : F) :
    let S := R.symm.toContinuousLinearMap
    let gbar₀ := S.adjoint (H (S xbar₀) + c)
    algorithm_5_1_3 R H c xbar₀ 0 = ⟨xbar₀, -gbar₀, -gbar₀⟩ := by
  simp [algorithm_5_1_3, CG.init, map_add, sub_eq_add_neg, add_comm]

/-- The transformed iterates satisfy (5.1.46)–(5.1.50) with the book's
gradient sign. -/
theorem algorithm_5_1_3_succ {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (c : E) (xbar₀ : F) (k : ℕ) :
    let S := R.symm.toContinuousLinearMap
    let A := S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap
    let s := algorithm_5_1_3 R H c xbar₀ k
    let g := -s.r
    let α := ‖g‖ ^ 2 / ⟪s.p, A s.p⟫
    let g' := g + α • A s.p
    let β := ‖g'‖ ^ 2 / ‖g‖ ^ 2
    algorithm_5_1_3 R H c xbar₀ (k + 1) = ⟨s.x + α • s.p, -g', -g' + β • s.p⟩ := by
  intro S A s g α g' β
  change CG.iterate A (-(S.adjoint c)) xbar₀ (k + 1) = _
  rw [CG.iterate_succ]
  change CG.step A s = _
  have hα : CG.alpha A s = α := by
    rw [CG.alpha, real_inner_self_eq_norm_sq, real_inner_comm s.p (A s.p)]
    simp only [α, g, norm_neg]
  have hr : (CG.step A s).r = -g' := by
    rw [CG.step_r, hα]
    change s.r - α • A s.p = -(-s.r + α • A s.p)
    abel
  have hβ : CG.beta A s = β := by
    rw [CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hr]
    simp [β, g]
  cases he : CG.step A s with
  | mk x r p =>
    have hx := CG.step_x A s
    have hp := CG.step_p A s
    rw [he, hα] at hx
    rw [hβ, hr, he] at hp
    rw [he] at hr
    simp only at hx hr hp
    rw [hx, hr, hp]

/-- The preconditioner induced by the transformation, `M = Rᵀ R`
in (5.1.53). -/
noncomputable def transformedCGPreconditioner {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) : E →L[ℝ] E :=
  R.toContinuousLinearMap.adjoint.comp R.toContinuousLinearMap

/-- The inverse preconditioner applies `R⁻¹R⁻ᵀ`, as in the
implicit realization of transformed CG. -/
theorem transformedCGPreconditioner_apply_inverse {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (x : E) :
    let S := R.symm.toContinuousLinearMap
    transformedCGPreconditioner R (S (S.adjoint x)) = x := by
  let S := R.symm.toContinuousLinearMap
  let L := R.toContinuousLinearMap
  have hSL : S.comp L = ContinuousLinearMap.id ℝ E :=
    ContinuousLinearMap.ext R.symm_apply_apply
  have h := congrArg ContinuousLinearMap.adjoint hSL
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at h
  change L.adjoint (R (R.symm (S.adjoint x))) = x
  rw [R.apply_symm_apply]
  exact congrArg (fun T : E →L[ℝ] E => T x) h

/-- Algorithm 5.1.4. The state of the preconditioned conjugate gradient recurrence.
The library stores the residual `-gₖ` and evaluates the preconditioned gradient
through the given inverse when needed. -/
noncomputable abbrev algorithm_5_1_4 (H Minv : E →ₗ[ℝ] E) (c x₀ : E) (k : ℕ) : PCG.State E :=
  PCG.iterate H Minv (-c) x₀ k

/-- Lemma 5.1.1. The critical point on the affine subspace parametrized by `S` is
`x - S (S* H S)⁻¹ S* (H x + c)`. An invertible compressed Hessian is represented
by the linear equivalence `B`. Positive definiteness on the parameter space makes
the critical point a minimizer. -/
theorem lemma_5_1_1 [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (S : F →L[ℝ] E) (B : F ≃L[ℝ] F) (hB : ∀ z, B z = S.adjoint (H (S z)))
    (c x : E) :
    let xS := x - S (B.symm (S.adjoint (H x + c)))
    xS ∈ Set.range (fun z : F => x + S z) ∧
      S.adjoint (H xS + c) = 0 ∧
      (∀ z : F, S.adjoint (H (x + S z) + c) = 0 → x + S z = xS) ∧
      ((∀ z : F, z ≠ 0 → 0 < ⟪z, B z⟫) →
        IsMinOn (quadraticObjective c H) (Set.range (fun z : F => x + S z)) xS) := by
  let t := B.symm (S.adjoint (H x + c))
  let xS := x - S t
  have hxS : xS = x + S (-t) := by simp [xS, sub_eq_add_neg]
  have hcoord (z : F) : S.adjoint (H (x + S z) + c) = B z + S.adjoint (H x + c) := by
    simp only [map_add, hB]
    abel
  have ht : B t = S.adjoint (H x + c) := B.apply_symm_apply _
  have hcrit : S.adjoint (H xS + c) = 0 := by
    rw [hxS, hcoord, map_neg, ht, neg_add_cancel]
  refine ⟨⟨-t, hxS.symm⟩, hcrit, ?_, ?_⟩
  · intro z hz
    rw [hcoord] at hz
    have heq : z = -t := B.injective (by rw [map_neg, ht]; exact eq_neg_iff_add_eq_zero.mpr hz)
    rw [heq, ← hxS]
  · intro hpos
    rw [isMinOn_iff]
    rintro _ ⟨z, rfl⟩
    have heq : x + S z = xS + S (z + t) := by
      dsimp [xS]
      rw [map_add]
      abel
    have hlin : ⟪c + H xS, S (z + t)⟫ = 0 := by
      rw [add_comm c, ← S.adjoint_inner_left, hcrit, inner_zero_left]
    have hquad : 0 ≤ ⟪S (z + t), H (S (z + t))⟫ := by
      rw [← S.adjoint_inner_right, ← hB]
      by_cases hz : z + t = 0
      · simp [hz]
      · exact (hpos _ hz).le
    change Subproblem.quadModel c H xS ≤ Subproblem.quadModel c H (x + S z)
    rw [heq, Subproblem.quadModel_add hH xS (S (z + t)), hlin, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hquad)

/-- Lemma 5.1.2. Appending a direction conjugate to the preceding ones updates the
affine minimizer by one exact line step. It is enough for the quadratic form to be
nonnegative on the enlarged span, with nonzero curvature in the new direction. -/
theorem lemma_5_1_2 (H : E →L[ℝ] E) (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (c x₀ xk : E) (p : ℕ → E) (k : ℕ)
    (hxk : xk - x₀ ∈ Submodule.span ℝ (p '' Set.Iio k))
    (hmin : IsMinOn (quadraticObjective c H)
      {x | x - x₀ ∈ Submodule.span ℝ (p '' Set.Iio k)} xk)
    (hconj : ∀ i < k, ⟪p i, H (p k)⟫ = 0)
    (hcurv : ⟪p k, H (p k)⟫ ≠ 0)
    (hpos : ∀ v ∈ Submodule.span ℝ (p '' Set.Iio (k + 1)), 0 ≤ ⟪v, H v⟫) :
    let σ := -⟪p k, H xk + c⟫ / ⟪p k, H (p k)⟫
    let x' := xk + σ • p k
    x' - x₀ ∈ Submodule.span ℝ (p '' Set.Iio (k + 1)) ∧
      H x' + c = H xk + c + σ • H (p k) ∧
      (∀ i ≤ k, ⟪p i, H x' + c⟫ = 0) ∧
      IsMinOn (quadraticObjective c H)
        {x | x - x₀ ∈ Submodule.span ℝ (p '' Set.Iio (k + 1))} x' := by
  let K := Submodule.span ℝ (p '' Set.Iio k)
  let K' := Submodule.span ℝ (p '' Set.Iio (k + 1))
  let σ := -⟪p k, H xk + c⟫ / ⟪p k, H (p k)⟫
  let x' := xk + σ • p k
  have hp (i : ℕ) (hi : i < k) : p i ∈ K :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  have hnonneg (v : E) (hv : v ∈ K) : 0 ≤ ⟪c + H xk, v⟫ := by
    refine Subproblem.inner_add_apply_nonneg_of_isMinOn hH hmin
      (Filter.Eventually.of_forall fun t => ?_)
    change xk + t • v - x₀ ∈ K
    rw [show xk + t • v - x₀ = (xk - x₀) + t • v by abel]
    exact K.add_mem hxk (K.smul_mem t hv)
  have hgrad (i : ℕ) (hi : i < k) : ⟪p i, H xk + c⟫ = 0 := by
    have hn := hnonneg (-p i) (K.neg_mem (hp i hi))
    rw [inner_neg_right] at hn
    rw [real_inner_comm, add_comm (H xk)]
    exact le_antisymm (neg_nonneg.mp hn) (hnonneg _ (hp i hi))
  have hformula : H x' + c = H xk + c + σ • H (p k) := by
    simp only [x', map_add, map_smul]
    abel
  have horth (i : ℕ) (hi : i ≤ k) : ⟪p i, H x' + c⟫ = 0 := by
    rw [hformula, inner_add_right, real_inner_smul_right]
    rcases hi.lt_or_eq with hik | rfl
    · rw [hgrad i hik, hconj i hik, mul_zero, add_zero]
    · dsimp [σ]
      rw [div_mul_cancel₀ _ hcurv, add_neg_cancel]
  have hsub : K ≤ K' := Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ k)))
  have hnew : x' - x₀ ∈ K' := by
    rw [show x' - x₀ = (xk - x₀) + σ • p k by dsimp [x']; abel]
    exact K'.add_mem (hsub hxk) (K'.smul_mem _ (Submodule.subset_span ⟨k, Nat.lt_succ_self k, rfl⟩))
  refine ⟨hnew, hformula, horth, ?_⟩
  have hker : K' ≤ LinearMap.ker ((innerSL ℝ (H x' + c)).toLinearMap) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    apply LinearMap.mem_ker.mpr
    change ⟪H x' + c, p i⟫ = 0
    rw [real_inner_comm]
    exact horth i (Nat.le_of_lt_succ hi)
  rw [isMinOn_iff]
  intro y hy
  let d := y - x'
  have hd : d ∈ K' := by
    rw [show d = (y - x₀) - (x' - x₀) by dsimp [d]; abel]
    exact K'.sub_mem hy hnew
  have hlin := hker hd
  change ⟪H x' + c, d⟫ = 0 at hlin
  have heq : y = x' + d := by dsimp [d]; abel
  have hquad := hpos d hd
  change Subproblem.quadModel c H x' ≤ Subproblem.quadModel c H y
  rw [heq, Subproblem.quadModel_add hH x' d, add_comm c, hlin, add_zero]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hquad)

/-- Lemma 5.1.3. A vector orthogonal to the generated directions is orthogonal to the
corresponding input vectors of the triangular recurrence. -/
theorem lemma_5_1_3 (y p : ℕ → E) (β : ℕ → ℕ → ℝ) (k : ℕ) (r : E)
    (h₀ : p 0 = y 0)
    (hrec : ∀ j < k, p (j + 1) = y (j + 1) + ∑ i ∈ Finset.range (j + 1), β j i • p i)
    (horth : ∀ i ≤ k, ⟪p i, r⟫ = 0) :
    ∀ i ≤ k, ⟪y i, r⟫ = 0 := by
  intro i hi
  cases i with
  | zero => rw [← h₀]; exact horth 0 hi
  | succ j =>
    have hsum : ⟪∑ i ∈ Finset.range (j + 1), β j i • p i, r⟫ = 0 := by
      rw [sum_inner]
      apply Finset.sum_eq_zero
      intro i hi'
      have hij := Finset.mem_range.mp hi'
      rw [real_inner_smul_left, horth i (by omega), mul_zero]
    have h := horth (j + 1) hi
    rw [hrec j (by omega), inner_add_left, hsum, add_zero] at h
    exact h

/-- The exact line step for the gradient-like residual in (5.1.14)–(5.1.15). -/
noncomputable def residualLineStep (H : E →ₗ[ℝ] E) (p r : E) : E :=
  r + (-⟪p, r⟫ / ⟪p, H p⟫) • H p

/-- Lemma 5.1.4. Exact residual line steps make the residual orthogonal to the
directions already used. The directional curvatures must be nonzero for the
quotients in (5.1.14). -/
theorem lemma_5_1_4 (H : E →ₗ[ℝ] E) (p r : ℕ → E) (k : ℕ)
    (hconj : ∀ i j, i < j → j ≤ k → ⟪p i, H (p j)⟫ = 0)
    (hnz : ∀ j ≤ k, ⟪p j, H (p j)⟫ ≠ 0)
    (hrec : ∀ j ≤ k, r (j + 1) = residualLineStep H (p j) (r j)) :
    ∀ i ≤ k, ⟪p i, r (k + 1)⟫ = 0 := by
  have horth (j : ℕ) (hj : j ≤ k + 1) : ∀ i < j, ⟪p i, r j⟫ = 0 := by
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      intro i hi
      have hj' : j ≤ k := by omega
      rw [hrec j hj', residualLineStep, inner_add_right, real_inner_smul_right]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | heq
      · rw [ih (by omega) i hij, hconj i j hij hj', mul_zero, add_zero]
      · subst i
        rw [div_mul_cancel₀ _ (hnz j hj'), add_neg_cancel]
  intro i hi
  exact horth (k + 1) le_rfl i (Nat.lt_succ_of_le hi)

/-- Lemma 5.1.5. Orthogonality to the preceding residuals reduces the conjugacy
update to the last direction. The residual pairings in (5.1.17) must be nonzero
to recover the individual conjugacy coefficients from residual differences. -/
theorem lemma_5_1_5 (H : E →ₗ[ℝ] E) (p r : ℕ → E) (k : ℕ) (y : E)
    (hconj : ∀ j < k, ⟪p k, H (p j)⟫ = 0)
    (hcurv : ∀ j ≤ k, ⟪p j, H (p j)⟫ ≠ 0)
    (hpair : ∀ j ≤ k, ⟪p j, r j⟫ ≠ 0)
    (hrec : ∀ j ≤ k, r (j + 1) = residualLineStep H (p j) (r j))
    (hy : ∀ j ≤ k, ⟪y, r j⟫ = 0) :
    ∀ j ≤ k, ⟪y + (⟪y, r (k + 1)⟫ / ⟪p k, r k⟫) • p k, H (p j)⟫ = 0 := by
  have hid (j : ℕ) (hj : j ≤ k) :
      ⟪y, r (j + 1)⟫ = (-⟪p j, r j⟫ / ⟪p j, H (p j)⟫) * ⟪y, H (p j)⟫ := by
    rw [hrec j hj, residualLineStep, inner_add_right, real_inner_smul_right, hy j hj, zero_add]
  intro j hj
  rw [inner_add_left, real_inner_smul_left]
  rcases hj.lt_or_eq with hjk | heq
  · have hz := hid j hj
    rw [hy _ (by omega)] at hz
    have hcoef := div_ne_zero (neg_ne_zero.mpr (hpair j hj)) (hcurv j hj)
    have hinner := (mul_eq_zero.mp hz.symm).resolve_left hcoef
    rw [hinner, hconj j hjk, mul_zero, add_zero]
  · subst j
    rw [hid k le_rfl]
    field_simp [hpair k le_rfl, hcurv k le_rfl]
    ring

/-- A counterexample to Lemma 5.1.5 without the nonzero earlier residual
pairings, even with a positive definite Hessian and a defined last coefficient.
Here the Hessian is the identity. The first residual increment vanishes, so
orthogonality to the residuals gives no information about the first direction. -/
theorem counterexample_5_1_5 :
    ∃ p₀ p₁ r₀ r₁ r₂ y : EuclideanSpace ℝ (Fin 3),
      ⟪p₀, p₁⟫ = 0 ∧ ⟪p₀, p₀⟫ ≠ 0 ∧ ⟪p₁, p₁⟫ ≠ 0 ∧
      r₁ = residualLineStep 1 p₀ r₀ ∧ r₂ = residualLineStep 1 p₁ r₁ ∧
      ⟪p₁, r₁⟫ ≠ 0 ∧ y ∉ Submodule.span ℝ {p₀, p₁} ∧
      ⟪y, r₀⟫ = 0 ∧ ⟪y, r₁⟫ = 0 ∧
      ⟪y + (⟪y, r₂⟫ / ⟪p₁, r₁⟫) • p₁, p₀⟫ ≠ 0 := by
  let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  have he (i j : Fin 3) : ⟪e i, e j⟫ = if i = j then 1 else 0 := by
    simp [e, EuclideanSpace.inner_single_left, PiLp.single_apply]
  have hnorm (i : Fin 3) : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
  have hne (i : Fin 3) : e i ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  have hspan : e 0 + e 2 ∉ Submodule.span ℝ {e 0, e 1} := by
    let L := (innerSL ℝ (e 2)).toLinearMap
    have hker : Submodule.span ℝ {e 0, e 1} ≤ LinearMap.ker L := by
      refine Submodule.span_le.mpr ?_
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [hz]
        exact LinearMap.mem_ker.mpr (by change ⟪e 2, e 0⟫ = 0; norm_num [he])
      · rw [Set.mem_singleton_iff.mp hz]
        exact LinearMap.mem_ker.mpr (by change ⟪e 2, e 1⟫ = 0; norm_num [he])
    intro hy
    have h := LinearMap.mem_ker.mp (hker hy)
    change ⟪e 2, e 0 + e 2⟫ = 0 at h
    norm_num [inner_add_right, he, hne] at h
  refine ⟨e 0, e 1, e 1, e 1, 0, e 0 + e 2, ?_, ?_, ?_, ?_, ?_, ?_, hspan, ?_, ?_, ?_⟩ <;>
    norm_num [residualLineStep, inner_add_left, he, hnorm, hne]

/-- Theorem 5.1.6. Conjugate gradients reach the exact solution in at most the
number of distinct eigenvalues. The finite set may also contain extra values, in
which case its cardinality is still an upper bound on the number of steps. -/
theorem theorem_5_1_6 [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetricCoercive) {c x₀ xstar : E} (hstar : H xstar = -c)
    (S : Finset ℝ) (hS : ∀ μ, Module.End.HasEigenvalue H μ → μ ∈ S) :
    (algorithm_5_1_2 H c x₀ S.card).x = xstar := by
  have hmem : -c - H x₀ ∈ LinearMap.range H :=
    ⟨xstar - x₀, by rw [map_sub, hstar]⟩
  have hgrade := Lanczos.grade_le_card_eigenvalues_of_mem_range hH.isSymmetric
    (fun μ _ hμ => hS μ hμ) hmem
  have happly := (CG.isGalerkinIterate (-c) x₀ hH S.card).apply_eq_of_grade_le hgrade
  exact hH.isCoercive.injective (happly.trans hstar.symm)

/-- Theorem 5.1.7. The energy-norm error of the conjugate gradient iteration satisfies the
Chebyshev bound for a positive spectral interval. The ratio of the endpoints is the spectral
condition number when the endpoints are the extreme eigenvalues. The product form includes
the case of an exact initial iterate. -/
theorem theorem_5_1_7 {H : E →ₗ[ℝ] E} {c x₀ xstar : E} (hstar : H xstar = -c)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hH : H.IsSymmetricBoundedBy lmin lmax) (k : ℕ) :
    energyNorm H ((algorithm_5_1_2 H c x₀ k).x - xstar) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm H (x₀ - xstar) := by
  rw [energyNorm_sub_comm H _ xstar, energyNorm_sub_comm H x₀ xstar]
  exact IsGalerkinIterate.energyNorm_error_le hl hll hH
    (CG.isGalerkinIterate (-c) x₀ (hH.isSymmetricCoercive hl) k) hstar

/-- Corollary 5.1.8. Preconditioned conjugate gradients obey the same energy-norm error
bound, with the interval given by the generalized eigenvalues of the pair `(H, M)`.
Taking the endpoints to be the extreme generalized eigenvalues gives the spectral
condition number of `M⁻¹ H`. -/
theorem corollary_5_1_8 {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (hH : H.IsSymmetric) {c x₀ xstar : E} (hstar : H xstar = -c)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : E, lmin * ⟪M x, x⟫ ≤ ⟪H x, x⟫)
    (hmax : ∀ x : E, ⟪H x, x⟫ ≤ lmax * ⟪M x, x⟫) (k : ℕ) :
    energyNorm H ((algorithm_5_1_4 H Minv c x₀ k).x - xstar) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm H (x₀ - xstar) := by
  rw [energyNorm_sub_comm H _ xstar, energyNorm_sub_comm H x₀ xstar]
  exact PCG.energyNorm_error_le hM hH hl hll hmin hmax hstar k

/-- Corollary 5.1.9. Preconditioned conjugate gradients reach the exact solution in
at most the number of distinct eigenvalues of the preconditioned operator. -/
theorem corollary_5_1_9 [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric)
    {l : ℝ} (hl : 0 < l) (hlo : ∀ x : E, l * ⟪M x, x⟫ ≤ ⟪H x, x⟫)
    {c x₀ xstar : E} (hstar : H xstar = -c)
    (S : Finset ℝ) (hS : ∀ μ, Module.End.HasEigenvalue (Minv ∘ₗ H) μ → μ ∈ S) :
    (algorithm_5_1_4 H Minv c x₀ S.card).x = xstar := by
  let B := hM.energyEnd (Minv ∘ₗ H)
  have hB : B.IsSymmetricCoercive := hM.isSymmetricCoercive_energyEnd H hH hl hlo
  have hS' (μ : ℝ) (hμ : Module.End.HasEigenvalue B μ) : μ ∈ S := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨u, rfl⟩ := hM.toEnergy.surjective v
    have hu : u ≠ 0 := by
      intro hu
      exact (Module.End.hasEigenvector_iff.mp hv).2 (by simp [hu])
    have heq := hv.apply_eq_smul
    change hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy u) = μ • hM.toEnergy u at heq
    rw [IsPreconditioner.energyEnd_apply, ← map_smul] at heq
    have huv : Module.End.HasEigenvector (Minv ∘ₗ H) μ u :=
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hM.toEnergy.injective heq), hu⟩
    exact hS μ (Module.End.hasEigenvalue_of_hasEigenvector huv)
  have hstar' : B (hM.toEnergy xstar) = -hM.toEnergy (Minv c) := by
    simp [B, LinearMap.comp_apply, hstar]
  have h := theorem_5_1_6 hB hstar' S hS' (x₀ := hM.toEnergy x₀)
  apply hM.toEnergy.injective
  rw [PCG.toEnergy_iterate_x H Minv (-c) x₀ hM S.card]
  simpa only [B, map_neg] using h

end ConnGouldToint.Chapter05
