import NumlibSurface.CartisGouldToint.Chapter07.Section01
import Numlib.Optimization.PenaltyCalculus
import Numlib.Analysis.Calculus.Gradient

/-!
# Chapter 7, Section 2: penalty and barrier models

The reciprocal penalty convention and minus-sign multiplier convention are matched to
the existing canonical objectives. Barrier identities require genuine strict positivity.
-/

noncomputable section
namespace CartisGouldToint.Chapter07.Section02
variable {n m : ℕ}

/-- The quadratic penalty `f + ||c||^2/(2 mu)` in Section 7.2.3.2. -/
def quadraticPenaltyModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (mu : ℝ) :=
  Constrained.penalized f c mu⁻¹

/-- Conversion to the source's reciprocal-parameter expression. -/
theorem quadraticPenaltyModel_eq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (mu : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    quadraticPenaltyModel f c mu x = f x + ‖c x‖ ^ 2 / (2 * mu) := by
  simp only [quadraticPenaltyModel, Constrained.penalized, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The quadratic-penalty multiplier used in (7.2.57). -/
def quadraticPenaltyMultiplier (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (mu : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  -(mu⁻¹ • c x)

/-- The penalty multiplier satisfies the actual perturbed constraint equation. -/
theorem quadraticPenaltyMultiplier_perturbed {c : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin m)} {mu : ℝ} (hmu : mu ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    c x = -mu • quadraticPenaltyMultiplier c mu x := by
  simp [quadraticPenaltyMultiplier, smul_smul, hmu]

/-- For a positive penalty parameter the constraint norm is the scaled multiplier norm. -/
theorem norm_constraint_eq_mul_norm_penaltyMultiplier
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {mu : ℝ} (hmu : 0 < mu)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖c x‖ = mu * ‖quadraticPenaltyMultiplier c mu x‖ := by
  calc
    ‖c x‖ = ‖-mu • quadraticPenaltyMultiplier c mu x‖ :=
      congrArg norm (quadraticPenaltyMultiplier_perturbed (c := c) (ne_of_gt hmu) x)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hmu]

/-- The actual quadratic-penalty derivative is the Lagrangian derivative at its multiplier. -/
theorem quadraticPenaltyModel_hasFDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x) (mu : ℝ) :
    HasFDerivAt (quadraticPenaltyModel f c mu)
      (f' - (innerSL ℝ (quadraticPenaltyMultiplier c mu x)).comp c') x := by
  convert Constrained.penalized_hasFDerivAt hf hc mu⁻¹ using 1
  · rfl
  · ext v
    simp [quadraticPenaltyMultiplier, ContinuousLinearMap.comp_apply]

/-- The augmented Lagrangian in Section 7.2.3.3, with the source multiplier sign. -/
def augmentedLagrangianModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) (mu : ℝ) := Constrained.augmented f c mu⁻¹ (-u)

/-- Conversion to the source's displayed augmented-Lagrangian formula. -/
theorem augmentedLagrangianModel_eq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) (mu : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    augmentedLagrangianModel f c u mu x =
      f x - inner ℝ u (c x) + ‖c x‖ ^ 2 / (2 * mu) := by
  simp only [augmentedLagrangianModel, Constrained.augmented, inner_neg_left,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The effective multiplier `u-c/mu` in (7.2.62). -/
def augmentedMultiplier (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) (mu : ℝ) (x : EuclideanSpace ℝ (Fin n)) :=
  u - mu⁻¹ • c x

/-- The effective augmented multiplier satisfies the perturbed constraint equation. -/
theorem augmentedMultiplier_perturbed {c : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin m)} (u : EuclideanSpace ℝ (Fin m)) {mu : ℝ} (hmu : mu ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) : c x = mu • (u - augmentedMultiplier c u mu x) := by
  simp [augmentedMultiplier, smul_smul, hmu]

/-- The actual augmented-Lagrangian derivative at its effective multiplier. -/
theorem augmentedLagrangianModel_hasFDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x)
    (u : EuclideanSpace ℝ (Fin m)) (mu : ℝ) :
    HasFDerivAt (augmentedLagrangianModel f c u mu)
      (f' - (innerSL ℝ (augmentedMultiplier c u mu x)).comp c') x := by
  convert Constrained.augmented_hasFDerivAt hf hc mu⁻¹ (-u) using 1
  · rfl
  · ext v
    simp [augmentedMultiplier, ContinuousLinearMap.comp_apply]
    ring

/-- One source augmented-Lagrangian update: contract infeasibility to retain the parameter,
or retain the multiplier and reduce the parameter. -/
def IsAugmentedUpdate (cOld cNew u uNext : EuclideanSpace ℝ (Fin m))
    (mu muNext tau gamma : ℝ) : Prop :=
  tau ∈ Set.Ioo 0 1 ∧ gamma ∈ Set.Ioo 0 1 ∧
    ((‖cNew‖ ≤ tau * ‖cOld‖ ∧ uNext = u - mu⁻¹ • cNew ∧ muNext = mu) ∨
    (tau * ‖cOld‖ < ‖cNew‖ ∧ uNext = u ∧ 0 < muNext ∧ muNext ≤ gamma * mu))

/-- A positive current parameter stays positive under an admissible update. -/
theorem IsAugmentedUpdate.parameter_pos {cOld cNew u uNext : EuclideanSpace ℝ (Fin m)}
    {mu muNext tau gamma : ℝ} (h : IsAugmentedUpdate cOld cNew u uNext mu muNext tau gamma)
    (hmu : 0 < mu) : 0 < muNext := by
  rcases h.2.2 with ⟨_, _, rfl⟩ | ⟨_, _, hnext, _⟩
  · exact hmu
  · exact hnext

/-- The strict barrier domain, allowing the source's shifted constraints. -/
def shiftedBarrierDomain (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (beta : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Constrained.barrierDomain (fun i x => c x i + beta)

/-- The source logarithmic barrier, with `beta=0` for the unshifted version. -/
def logarithmicBarrierModel (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (mu : ℝ) (beta : ℝ := 0) :=
  Constrained.logarithmicBarrier f (fun i x => c x i + beta) mu

/-- The strict barrier domain retains every positive shifted constraint. -/
@[simp] theorem mem_shiftedBarrierDomain {c : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin m)} {beta : ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ shiftedBarrierDomain c beta ↔ ∀ i, 0 < c x i + beta := Iff.rfl

/-- The componentwise barrier multiplier. -/
def barrierMultiplier (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (mu beta : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => mu / (c x i + beta))

/-- Every shifted complementarity product is exactly the barrier parameter. -/
theorem barrierMultiplier_complementarity {c : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin m)} {beta : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ shiftedBarrierDomain c beta) (mu : ℝ) (i : Fin m) :
    (c x i + beta) * barrierMultiplier c mu beta x i = mu := by
  change (c x i + beta) * (mu / (c x i + beta)) = mu
  field_simp [ne_of_gt (hx i)]

/-- Positive barrier parameters give positive multipliers on the strict domain. -/
theorem barrierMultiplier_pos {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {beta mu : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ shiftedBarrierDomain c beta)
    (hmu : 0 < mu) (i : Fin m) : 0 < barrierMultiplier c mu beta x i :=
  div_pos hmu (hx i)

/-- The Euclidean squared complementarity norm counts every actual constraint component. -/
theorem barrierMultiplier_complementarity_norm_sq {c : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin m)} {beta : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ shiftedBarrierDomain c beta) (mu : ℝ) :
    ‖(WithLp.toLp 2 (fun i => (c x i + beta) * barrierMultiplier c mu beta x i) :
      EuclideanSpace ℝ (Fin m))‖ ^ 2 = (m : ℝ) * mu ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, barrierMultiplier_complementarity hx]

/-- The source choice `mu=epsilon/sqrt(m)` gives the exact Euclidean complementarity norm. -/
theorem barrierMultiplier_complementarity_norm {c : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin m)} {beta epsilon : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ shiftedBarrierDomain c beta) (hm : 0 < m) (he : 0 ≤ epsilon) :
    ‖(WithLp.toLp 2 (fun i => (c x i + beta) *
      barrierMultiplier c (epsilon / Real.sqrt m) beta x i) :
        EuclideanSpace ℝ (Fin m))‖ = epsilon := by
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hh := barrierMultiplier_complementarity_norm_sq hx (epsilon / Real.sqrt m)
  have hq : (m : ℝ) * (epsilon / Real.sqrt m) ^ 2 = epsilon ^ 2 := by
    rw [div_pow, ← mul_div_assoc, div_eq_iff (ne_of_gt (sq_pos_of_pos hs)),
      Real.sq_sqrt (Nat.cast_nonneg m)]
    ring
  rw [hq] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i =>
    (c x i + beta) * barrierMultiplier c (epsilon / Real.sqrt m) beta x i) :
      EuclideanSpace ℝ (Fin m))]

/-- The barrier derivative equals the source Lagrangian derivative at the barrier multiplier. -/
theorem logarithmicBarrierModel_hasFDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x) {beta : ℝ}
    (hx : x ∈ shiftedBarrierDomain c beta) (mu : ℝ) :
    HasFDerivAt (logarithmicBarrierModel f c mu beta)
      (f' - (innerSL ℝ (barrierMultiplier c mu beta x)).comp c') x := by
  have hci (i : Fin m) : HasFDerivAt (fun z => c z i + beta)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp c') x := by
    have hp : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin m) => v i)
        (EuclideanSpace.proj (𝕜 := ℝ) i) (c x) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    exact (hp.comp x hc).add_const beta
  convert Constrained.logarithmicBarrier_hasFDerivAt hf hci hx mu using 1
  · rfl
  · ext v
    simp [EuclideanSpace.innerSL_eq_sum_smul_proj, barrierMultiplier,
      ContinuousLinearMap.comp_apply]

/-- The penalty and the earlier source Lagrangian have the same actual primal derivative. -/
theorem quadraticPenaltyModel_fderiv_eq_lagrangian {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (mu : ℝ) :
    fderiv ℝ (quadraticPenaltyModel f c mu) x =
      fderiv ℝ (fun z => Section01.lagrangian f c z (quadraticPenaltyMultiplier c mu x)) x :=
  (quadraticPenaltyModel_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt mu).fderiv.trans
    (Section01.lagrangian_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt _).fderiv.symm

/-- The augmented objective and the source Lagrangian have the same actual primal derivative. -/
theorem augmentedLagrangianModel_fderiv_eq_lagrangian {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (u : EuclideanSpace ℝ (Fin m)) (mu : ℝ) :
    fderiv ℝ (augmentedLagrangianModel f c u mu) x =
      fderiv ℝ (fun z => Section01.lagrangian f c z (augmentedMultiplier c u mu x)) x :=
  (augmentedLagrangianModel_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt u mu).fderiv.trans
    (Section01.lagrangian_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt _).fderiv.symm

/-- On the strict domain, the barrier and source Lagrangian derivatives agree. -/
theorem logarithmicBarrierModel_fderiv_eq_lagrangian {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) {beta : ℝ} (hx : x ∈ shiftedBarrierDomain c beta)
    (mu : ℝ) : fderiv ℝ (logarithmicBarrierModel f c mu beta) x =
      fderiv ℝ (fun z => Section01.lagrangian f c z (barrierMultiplier c mu beta x)) x :=
  (logarithmicBarrierModel_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt hx mu).fderiv.trans
    (Section01.lagrangian_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt _).fderiv.symm

end CartisGouldToint.Chapter07.Section02
