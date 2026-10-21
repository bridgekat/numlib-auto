import Numlib.Optimization.SecularStepDerivatives
import NumlibSurface.CartisGouldToint.Chapter08.Section01
import Numlib.Optimization.WeightedSecularResolvent
import Numlib.Optimization.SecularPowers
import Numlib.Analysis.Convex.SupportingLine

/-!
# Chapter 8, Section 2: secular functions and subproblem optimality

The secular function uses the actual inverse of the shifted matrix in an arbitrary SPD metric.
The generalized spectral representation, boundary-root theorem, and all-order Taylor bounds
are derived by transport to the energy inner product. Theorems 8.2.7 and 8.2.8 include all
stationarity, positive semidefiniteness, complementarity, and strict uniqueness clauses.
-/

open scoped InnerProductSpace Topology
open Filter
open Set
open Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01

namespace CartisGouldToint.Chapter08.Section02
open Optimization.SecularResolvent

variable {n : ℕ} {g s : EuclideanSpace ℝ (Fin n)}
  {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The source shifted matrix is exactly the shifted operator. -/
theorem toEuclideanLin_metric_shift (lambda : ℝ) :
    Matrix.toEuclideanLin (H + lambda • M) =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap +
        lambda • Matrix.toEuclideanLin M := by
  rw [map_add, map_smul]
  rfl

/-- The original matrix shifted system is the additive stationarity equation. -/
theorem metric_shift_stationary_iff (lambda : ℝ) :
    g + Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H s +
        lambda • Matrix.toEuclideanLin M s = 0 ↔
        Matrix.toEuclideanLin (H + lambda • M) s = -g := by
  rw [toEuclideanLin_metric_shift]
  change g + Matrix.toEuclideanLin H s + lambda • Matrix.toEuclideanLin M s = 0 ↔
    Matrix.toEuclideanLin H s + lambda • Matrix.toEuclideanLin M s = -g
  constructor
  · intro h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_assoc, add_comm, add_left_comm] using h
  · intro h
    rw [add_assoc, h, add_neg_cancel]

/-- The self-adjoint preconditioned Hessian for the generalized eigenvalue pencil `(H,M)`. -/
noncomputable abbrev secularHessian (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :=
  (energyHessian hM.isPreconditioner_toEuclideanLin
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)).toLinearMap

/-- Symmetry of the generalized Hessian follows from symmetry of `H` and positivity of `M`. -/
theorem secularHessian_isSymmetric (hH : H.IsSymm) (hM : M.PosDef) :
    (secularHessian H hM).IsSymmetric :=
  isSymmetric_energyHessian hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin

/-- The generalized eigenvalues, obtained from the energy-space spectral theorem. -/
noncomputable abbrev secularEigenvalues (hH : H.IsSymm) (hM : M.PosDef) :=
  (secularHessian_isSymmetric hH hM).eigenvalues rfl

/-- The source cutoff `max(0,-λ₁)`, expressed as the maximum of all nonnegative spectral shifts.
This definition also covers the empty spectrum in dimension zero. -/
noncomputable def secularThreshold (hH : H.IsSymm) (hM : M.PosDef) : ℝ :=
  ((Finset.univ.sup fun i =>
    (⟨max 0 (-secularEigenvalues hH hM i), le_max_left _ _⟩ : NNReal)) : NNReal)

/-- Every generalized eigenvalue is nonnegative after shifting by the cutoff. -/
theorem secularThreshold_add_eigenvalue_nonneg (hH : H.IsSymm) (hM : M.PosDef) (i) :
    0 ≤ secularThreshold hH hM + secularEigenvalues hH hM i := by
  have hi := Finset.le_sup (f := fun j =>
    (⟨max 0 (-secularEigenvalues hH hM j), le_max_left _ _⟩ : NNReal))
    (Finset.mem_univ i)
  have hh : max 0 (-secularEigenvalues hH hM i) ≤ secularThreshold hH hM := hi
  linarith [le_max_right 0 (-secularEigenvalues hH hM i)]

/-- The actual source solution `s(λ)=−(H+λM)⁻¹g`. -/
noncomputable def secularStep (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  -Ring.inverse (Matrix.toEuclideanLin (H + t • M)) g

/-- The secular function (8.2.4), with the actual inverse of the original shifted matrix. -/
noncomputable def secularData (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  weightedNorm M (secularStep g H M t) ^ 2

/-- The transformed secular function (8.2.17). -/
noncomputable def transformedSecularFunction (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (β t : ℝ) : ℝ := secularData g H M t ^ β

/-- Identification with the metric resolvent, including the immaterial minus sign in the step. -/
theorem secularData_eq_weightedResolvent (t : ℝ) :
    secularData g H M t = Optimization.SecularResolvent.weightedNormSqResolvent
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap
      (Matrix.toEuclideanLin M) g t := by
  simp only [secularData, secularStep, weightedNorm_eq_energyNorm,
    toEuclideanLin_metric_shift, Optimization.SecularResolvent.weightedNormSqResolvent]
  simp [energyNorm]

/-- Above the cutoff all energy-space shifted eigenvalues are strictly positive. -/
theorem secular_admissible (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (ht : secularThreshold hH hM < t) :
    Optimization.SecularResolvent.Admissible (secularHessian_isSymmetric hH hM) t := by
  intro i
  have := secularThreshold_add_eigenvalue_nonneg hH hM i
  change 0 < t + secularEigenvalues hH hM i
  linarith

/-- The matrix secular function is exactly the energy-space resolvent on the source domain. -/
theorem secularData_eq_resolvent (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (ht : secularThreshold hH hM < t) :
    secularData g H M t = Optimization.SecularResolvent.normSqResolvent
      (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) t := by
  rw [secularData_eq_weightedResolvent]
  apply Optimization.SecularResolvent.weightedNormSqResolvent_eq
  exact Optimization.SecularResolvent.isUnit_shift (secularHessian_isSymmetric hH hM) t
    (fun i => ne_of_gt (secular_admissible hH hM ht i))

/-- The generalized eigenvectors in the original coordinates, with no supplied factorization. -/
noncomputable def secularEigenvector (hH : H.IsSymm) (hM : M.PosDef)
    (i : Fin (Module.finrank ℝ hM.isPreconditioner_toEuclideanLin.EnergySpace)) :
    EuclideanSpace ℝ (Fin n) :=
  hM.isPreconditioner_toEuclideanLin.toEnergy.symm
    ((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl i)

/-- The generalized eigenvectors are orthonormal in the original matrix metric. -/
theorem secularEigenvector_orthonormal (hH : H.IsSymm) (hM : M.PosDef) (i j) :
    inner ℝ (Matrix.toEuclideanLin M (secularEigenvector hH hM i))
      (secularEigenvector hH hM j) = if i = j then 1 else 0 := by
  have hh := orthonormal_iff_ite.mp
    ((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).orthonormal
  have he : inner ℝ
      (hM.isPreconditioner_toEuclideanLin.toEnergy (secularEigenvector hH hM i))
      (hM.isPreconditioner_toEuclideanLin.toEnergy (secularEigenvector hH hM j)) =
      if i = j then 1 else 0 := by
    simpa only [secularEigenvector, LinearEquiv.apply_symm_apply] using hh i j
  simpa only [WithEnergy.inner_equiv, energyInner] using he

/-- The generalized eigenvectors satisfy `H vᵢ = λᵢ M vᵢ`, as in (8.2.5). -/
theorem secularEigenvector_equation (hH : H.IsSymm) (hM : M.PosDef) (i) :
    Matrix.toEuclideanLin H (secularEigenvector hH hM i) =
      secularEigenvalues hH hM i • Matrix.toEuclideanLin M (secularEigenvector hH hM i) := by
  have he := (secularHessian_isSymmetric hH hM).apply_eigenvectorBasis rfl i
  have hp : Matrix.toEuclideanLin M⁻¹
      (Matrix.toEuclideanLin H (secularEigenvector hH hM i)) =
      secularEigenvalues hH hM i • secularEigenvector hH hM i := by
    apply hM.isPreconditioner_toEuclideanLin.toEnergy.injective
    rw [map_smul]
    change secularHessian H hM
      (hM.isPreconditioner_toEuclideanLin.toEnergy (secularEigenvector hH hM i)) = _
    simpa only [secularEigenvector, LinearEquiv.apply_symm_apply,
      RCLike.ofReal_real_eq_id, id_eq] using he
  have hh := congrArg (Matrix.toEuclideanLin M) hp
  simpa only [hM.isPreconditioner_toEuclideanLin.apply_inv, map_smul] using hh

/-- The trust-region target in (8.2.9). -/
def trustRegionSecularTarget (delta : ℝ) (_t : ℝ) : ℝ := delta ^ 2

/-- The regularization target in (8.2.9). -/
noncomputable def regularizationSecularTarget (sigma r t : ℝ) : ℝ :=
  (t / sigma) ^ (2 / (r - 2))

/-- Raising both nonnegative sides to a nonzero power preserves the secular equation (8.2.16). -/
theorem transformedSecularFunction_eq_iff {β t τ : ℝ} (hβ : β ≠ 0) (hτ : 0 ≤ τ) :
    transformedSecularFunction g H M β t = τ ^ β ↔ secularData g H M t = τ :=
  Real.rpow_left_inj (sq_nonneg _) hτ hβ

/-- The coefficients in (8.2.7) are the original inner products `vᵢᵀg`. -/
theorem secular_coordinate (hH : H.IsSymm) (hM : M.PosDef) (i) :
    ((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) i =
      inner ℝ (secularEigenvector hH hM i) g := by
  rw [OrthonormalBasis.repr_apply_apply]
  have hh := hM.isPreconditioner_toEuclideanLin.inner_toEnergy_inv
    (secularEigenvector hH hM i) g
  simpa only [secularEigenvector, LinearEquiv.apply_symm_apply] using hh

/-- The actual inverse has the generalized spectral representation (8.2.7). -/
theorem secularData_eq_spectral (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (ht : secularThreshold hH hM < t) :
    secularData g H M t = ∑ i,
      (inner ℝ (secularEigenvector hH hM i) g) ^ 2 / (t + secularEigenvalues hH hM i) ^ 2 := by
  rw [secularData_eq_resolvent hH hM ht,
    Optimization.SecularResolvent.normSqResolvent_eq_spectralNormSq
      (secularHessian_isSymmetric hH hM) _ t
      (fun i => ne_of_gt (secular_admissible hH hM ht i))]
  unfold Optimization.SecularResolvent.spectralNormSq
  apply Finset.sum_congr rfl
  intro i _
  change (((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
    (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) i) ^ 2 /
    (t + secularEigenvalues hH hM i) ^ 2 = _
  rw [secular_coordinate]

/-- The actual source inverse solves (8.2.2) everywhere above the spectral cutoff. -/
theorem secularStep_stationary (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (ht : secularThreshold hH hM < t) :
    Matrix.toEuclideanLin (H + t • M) (secularStep g H M t) = -g := by
  have hu := Optimization.SecularResolvent.isUnit_metric_shift
    hM.isPreconditioner_toEuclideanLin
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
    (Optimization.SecularResolvent.isUnit_shift (secularHessian_isSymmetric hH hM) t
      (fun i => ne_of_gt (secular_admissible hH hM ht i)))
  have hh := congrArg (fun B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => B g)
    (Ring.mul_inverse_cancel _ hu)
  rw [secularStep, map_neg, toEuclideanLin_metric_shift]
  exact congrArg Neg.neg hh

/-- Lemma 8.2.1. The strict right-boundary comparison is stated as an eventual inequality,
so it applies both to finite right limits and to an infinite pole at the boundary. Nonzero,
nonnegative targets are expressed by nonnegativity and positivity at some point. -/
theorem lemma_8_2_1_of_eventual_boundary (hH : H.IsSymm) (hM : M.PosDef) {τ : ℝ → ℝ}
    (hτ : ContinuousOn τ (Ioi (secularThreshold hH hM)))
    (hmono : MonotoneOn τ (Ioi (secularThreshold hH hM)))
    (hnonneg : ∀ t ∈ Ioi (secularThreshold hH hM), 0 ≤ τ t)
    (hpos : ∃ t ∈ Ioi (secularThreshold hH hM), 0 < τ t)
    (hboundary : ∀ᶠ t in 𝓝[>] (secularThreshold hH hM), τ t < secularData g H M t) :
    ∃! t, t ∈ Ioi (secularThreshold hH hM) ∧ secularData g H M t = τ t := by
  have hg : g ≠ 0 := by
    intro hg0
    obtain ⟨t, hb, ht⟩ := (hboundary.and self_mem_nhdsWithin).exists
    have hn := hnonneg t ht
    rw [hg0] at hb
    simp only [secularData, secularStep, map_zero, neg_zero, weightedNorm,
      inner_zero_left, Real.sqrt_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at hb
    linarith
  have hroot := Optimization.SecularResolvent.existsUnique_secular_root_of_boundary
    (secularHessian_isSymmetric hH hM)
    (Optimization.SecularResolvent.toEnergy_inv_ne_zero hM.isPreconditioner_toEuclideanLin hg)
    (secularThreshold hH hM) (secularThreshold_add_eigenvalue_nonneg hH hM) hτ hmono
    (show ∀ᶠ t in 𝓝[>] (secularThreshold hH hM), τ t <
      Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) t by
      filter_upwards [hboundary, self_mem_nhdsWithin] with t hb ht
      rwa [← secularData_eq_resolvent hH hM ht]) hpos
  simpa only [show (fun t => t ∈ Ioi (secularThreshold hH hM) ∧ secularData g H M t = τ t) =
      (fun t => t ∈ Ioi (secularThreshold hH hM) ∧
        Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) t = τ t) by
    funext t
    by_cases ht : t ∈ Ioi (secularThreshold hH hM)
    · simp only [ht, true_and, secularData_eq_resolvent hH hM ht]
    · simp only [ht, false_and]] using hroot

/-- Lemma 8.2.1 with explicit finite or infinite right limits at the possibly singular cutoff.
In the infinite case the target still has a finite right limit. -/
theorem lemma_8_2_1 (hH : H.IsSymm) (hM : M.PosDef) {τ : ℝ → ℝ}
    (hτ : ContinuousOn τ (Ioi (secularThreshold hH hM)))
    (hmono : MonotoneOn τ (Ioi (secularThreshold hH hM)))
    (hnonneg : ∀ t ∈ Ioi (secularThreshold hH hM), 0 ≤ τ t)
    (hpos : ∃ t ∈ Ioi (secularThreshold hH hM), 0 < τ t)
    (hboundary :
      (∃ p q : ℝ, Tendsto (secularData g H M) (𝓝[>] (secularThreshold hH hM)) (𝓝 p) ∧
        Tendsto τ (𝓝[>] (secularThreshold hH hM)) (𝓝 q) ∧ q < p) ∨
      (∃ q : ℝ, Tendsto (secularData g H M) (𝓝[>] (secularThreshold hH hM)) atTop ∧
        Tendsto τ (𝓝[>] (secularThreshold hH hM)) (𝓝 q))) :
    ∃! t, t ∈ Ioi (secularThreshold hH hM) ∧ secularData g H M t = τ t := by
  apply lemma_8_2_1_of_eventual_boundary hH hM hτ hmono hnonneg hpos
  rcases hboundary with ⟨p, q, hp, hq, hqp⟩ | ⟨q, hp, hq⟩
  · exact hq.eventually_lt hp hqp
  · filter_upwards [hq.eventually_lt_const (show q < q + 1 by linarith),
      hp.eventually (eventually_gt_atTop (q + 1))] with t ht hπ
    exact ht.trans hπ

/-- The source Taylor polynomial (8.2.12), computed from the full derivatives of (8.2.4). -/
noncomputable def secularTaylor (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (c δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), iteratedDeriv j (secularData g H M) c * δ ^ j / j.factorial

/-- The Taylor polynomial of the original matrix function agrees with its energy-space version. -/
theorem secularTaylor_eq (hH : H.IsSymm) (hM : M.PosDef) (k : ℕ) {c : ℝ}
    (hc : secularThreshold hH hM < c) (δ : ℝ) :
    secularTaylor g H M k c δ = Optimization.SecularResolvent.taylorApprox
      (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k c (c + δ) := by
  have he : secularData g H M =ᶠ[𝓝 c] Optimization.SecularResolvent.normSqResolvent
      (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hc] with t ht
    exact secularData_eq_resolvent hH hM ht
  rw [secularTaylor, Optimization.SecularResolvent.taylorApprox_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [he.iteratedDeriv_eq j]
  simp only [add_sub_cancel_left]

/-- Theorem 8.2.2. All Taylor bounds (8.2.13)–(8.2.14), including their strict versions
for a nonzero gradient. The signed remainder encodes the even upper and odd lower bounds. -/
theorem theorem_8_2_2 (hH : H.IsSymm) (hM : M.PosDef) {c δ : ℝ}
    (hc : secularThreshold hH hM < c) (hx : secularThreshold hH hM < c + δ) :
    ((0 < δ → ∀ k : ℕ, 0 ≤ (-1 : ℝ) ^ (k + 1) *
      (secularData g H M (c + δ) - secularTaylor g H M k c δ)) ∧
    (δ < 0 → ∀ k : ℕ, secularTaylor g H M k c δ ≤ secularTaylor g H M (k + 1) c δ ∧
      secularTaylor g H M (k + 1) c δ ≤ secularData g H M (c + δ))) ∧
    (g ≠ 0 →
      (0 < δ → ∀ k : ℕ, 0 < (-1 : ℝ) ^ (k + 1) *
        (secularData g H M (c + δ) - secularTaylor g H M k c δ)) ∧
      (δ < 0 → ∀ k : ℕ, secularTaylor g H M k c δ < secularTaylor g H M (k + 1) c δ ∧
        secularTaylor g H M (k + 1) c δ < secularData g H M (c + δ))) := by
  have hnonneg := Optimization.SecularResolvent.normSqResolvent_taylor_bounds_nonneg
    (secularHessian_isSymmetric hH hM)
    (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
    (secular_admissible hH hM hc) (secular_admissible hH hM hx)
  have hvalue := secularData_eq_resolvent (g := g) hH hM hx
  have htaylor := fun k => secularTaylor_eq (g := g) hH hM k hc δ
  constructor
  · constructor
    · intro hδ k
      simpa only [hvalue, htaylor] using hnonneg.1 (by linarith) k
    · intro hδ k
      simpa only [hvalue, htaylor] using hnonneg.2 (by linarith) k
  · intro hg
    have hstrict := Optimization.SecularResolvent.normSqResolvent_taylor_bounds
      (secularHessian_isSymmetric hH hM)
      (Optimization.SecularResolvent.toEnergy_inv_ne_zero hM.isPreconditioner_toEuclideanLin hg)
      (secular_admissible hH hM hc) (secular_admissible hH hM hx)
    constructor
    · intro hδ k
      simpa only [hvalue, htaylor] using hstrict.1 (by linarith) k
    · intro hδ k
      simpa only [hvalue, htaylor] using hstrict.2 (by linarith) k

/-- Theorem 8.2.7, in the stronger necessary-and-sufficient form, with the uniqueness clause. -/
theorem theorem_8_2_7 (hH : H.IsSymm) (hM : M.PosDef) {delta : ℝ} (hdelta : 0 < delta) :
    (trustRegionMinimizer g H M delta s ↔
      weightedNorm M s ≤ delta ∧ ∃ lambda : ℝ, 0 ≤ lambda ∧
        Matrix.toEuclideanLin (H + lambda • M) s = -g ∧ (H + lambda • M).PosSemidef ∧
          lambda * (weightedNorm M s ^ 2 - delta ^ 2) = 0) ∧
    (∀ lambda : ℝ, trustRegionMinimizer g H M delta s →
      0 ≤ lambda → Matrix.toEuclideanLin (H + lambda • M) s = -g →
      (H + lambda • M).PosDef → lambda * (weightedNorm M s ^ 2 - delta ^ 2) = 0 →
      ∀ y, trustRegionMinimizer g H M delta y → y = s) := by
  have hHs : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).IsSymmetric :=
    hH.isSymmetric_toEuclideanLin
  have hm := hM.isPreconditioner_toEuclideanLin
  have hstat := fun lambda => metric_shift_stationary_iff (g := g) (s := s)
    (H := H) (M := M) lambda
  constructor
  · have hh := isMinOn_energy_ball_iff_shift hm hHs (g := g) (s := s) hdelta
    simpa only [trustRegionMinimizer, quadraticModel_eq_quadratic, weightedNorm_eq_energyNorm,
      hstat, ← toEuclideanLin_metric_shift, Matrix.isPositive_toEuclideanLin_iff] using hh
  · intro lambda hsmin hl hs hp hc y hy
    apply eq_of_energy_ball_shift_pos hm hHs
      (delta := delta) (lambda := lambda)
    · simpa only [weightedNorm_eq_energyNorm] using hy.1
    · exact hl
    · exact (hstat lambda).mpr hs
    · intro d hd
      have hh := hp.isSymmetricCoercive_toEuclideanLin.isCoercive.inner_self_pos hd
      simpa only [RCLike.re_to_real, real_inner_comm, toEuclideanLin_metric_shift] using hh
    · simpa only [weightedNorm_eq_energyNorm] using hc
    · simpa only [mem_ofPred_eq, quadraticModel_eq_quadratic] using hy.2 hsmin.1

/-- Theorem 8.2.8, with the full radial shift and uniqueness clauses. -/
theorem theorem_8_2_8 (hH : H.IsSymm) (hM : M.PosDef) {sigma r : ℝ}
    (hsigma : 0 < sigma) (hr : 2 < r) :
    (regularizedMinimizer g H M sigma r s ↔
      ∃ lambda : ℝ, lambda = sigma * weightedNorm M s ^ (r - 2) ∧
        Matrix.toEuclideanLin (H + lambda • M) s = -g ∧
          (H + lambda • M).PosSemidef) ∧
    (Matrix.PosDef (H + (sigma * weightedNorm M s ^ (r - 2)) • M) →
      regularizedMinimizer g H M sigma r s →
      ∀ y, regularizedMinimizer g H M sigma r y → y = s) := by
  have hHs : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).IsSymmetric :=
    hH.isSymmetric_toEuclideanLin
  have hm := hM.isPreconditioner_toEuclideanLin
  have hstat := fun lambda => metric_shift_stationary_iff (g := g) (s := s)
    (H := H) (M := M) lambda
  have hiff : regularizedMinimizer g H M sigma r s ↔
      Matrix.toEuclideanLin (H + (sigma * weightedNorm M s ^ (r - 2)) • M) s = -g ∧
        (H + (sigma * weightedNorm M s ^ (r - 2)) • M).PosSemidef := by
    have hh := isMinOn_energy_power_iff_shift hm hHs hsigma.le hr (g := g) (s := s)
    simpa only [regularizedMinimizer, regularizedModel_eq_weightedPowerQuadratic,
      weightedNorm_eq_energyNorm, hstat, ← toEuclideanLin_metric_shift,
      Matrix.isPositive_toEuclideanLin_iff] using hh
  constructor
  · constructor
    · intro hs
      exact ⟨_, rfl, (hiff.mp hs).1, (hiff.mp hs).2⟩
    · rintro ⟨lambda, rfl, hstat, hpos⟩
      exact hiff.mpr ⟨hstat, hpos⟩
  · intro hp hs y hy
    apply eq_of_energy_power_shift_pos hm hHs hsigma.le hr
    · apply (hstat _).mpr
      simpa only [weightedNorm_eq_energyNorm] using (hiff.mp hs).1
    · intro d hd
      have hh := hp.isSymmetricCoercive_toEuclideanLin.isCoercive.inner_self_pos hd
      simpa only [RCLike.re_to_real, real_inner_comm, toEuclideanLin_metric_shift,
        weightedNorm_eq_energyNorm] using hh
    · simpa only [mem_ofPred_eq, regularizedModel_eq_weightedPowerQuadratic] using hy (mem_univ s)

/-- On the regular domain the transformed source function is the energy resolvent power. -/
theorem transformedSecularFunction_eqOn (hH : H.IsSymm) (hM : M.PosDef) (β : ℝ) :
    EqOn (transformedSecularFunction g H M β)
      (fun t => Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) t ^ β)
      (Ioi (secularThreshold hH hM)) := by
  intro t ht
  rw [transformedSecularFunction, secularData_eq_resolvent hH hM ht]

/-- The transformed source function is smooth at every regular point for nonzero `g`. -/
theorem contDiffAt_transformedSecularFunction (hH : H.IsSymm) (hM : M.PosDef)
    (hg : g ≠ 0) (β : ℝ) {t : ℝ} (ht : secularThreshold hH hM < t)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k (transformedSecularFunction g H M β) t := by
  apply (Optimization.SecularResolvent.contDiffAt_rpow_normSqResolvent
    (secularHessian_isSymmetric hH hM)
    (Optimization.SecularResolvent.toEnergy_inv_ne_zero hM.isPreconditioner_toEuclideanLin hg)
    β (fun i => ne_of_gt (secular_admissible hH hM ht i)) k).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact transformedSecularFunction_eqOn hH hM β hx

/-- Corollary 8.2.4. Strict monotonicity, curvature, and limits at infinity of the transformed
secular function. The nonzero right-hand side makes negative powers meaningful. -/
theorem corollary_8_2_4 (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0) :
    (∀ β : ℝ, 0 < β →
      StrictAntiOn (transformedSecularFunction g H M β) (Ioi (secularThreshold hH hM)) ∧
      StrictConvexOn ℝ (Ioi (secularThreshold hH hM)) (transformedSecularFunction g H M β) ∧
      Tendsto (transformedSecularFunction g H M β) atTop (𝓝 0)) ∧
    (∀ β : ℝ, -(1 / 2 : ℝ) ≤ β → β < 0 →
      StrictMonoOn (transformedSecularFunction g H M β) (Ioi (secularThreshold hH hM)) ∧
      ConcaveOn ℝ (Ioi (secularThreshold hH hM)) (transformedSecularFunction g H M β) ∧
      Tendsto (transformedSecularFunction g H M β) atTop atTop) := by
  have hh := secularHessian_isSymmetric hH hM
  have hn := Optimization.SecularResolvent.toEnergy_inv_ne_zero
    hM.isPreconditioner_toEuclideanLin hg
  have ha := secularThreshold_add_eigenvalue_nonneg hH hM
  have he (β : ℝ) := transformedSecularFunction_eqOn (g := g) hH hM β
  have he' (β : ℝ) : transformedSecularFunction g H M β =ᶠ[atTop]
      (fun t => Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) t ^ β) := by
    filter_upwards [eventually_gt_atTop (secularThreshold hH hM)] with t ht
    exact he β ht
  constructor
  · intro β hb
    refine ⟨?_, (Optimization.SecularResolvent.strictConvexOn_rpow_normSqResolvent
      hh hn _ ha hb).congr (he β).symm, ?_⟩
    · intro x hx y hy hxy
      rw [he β hx, he β hy]
      exact Optimization.SecularResolvent.strictAntiOn_rpow_normSqResolvent
        hh hn _ ha hb hx hy hxy
    · exact (Optimization.SecularResolvent.tendsto_rpow_normSqResolvent_atTop
        hh _ hb).congr' (he' β).symm
  · intro β hb hb'
    refine ⟨?_, (Optimization.SecularResolvent.concaveOn_rpow_normSqResolvent
      hh hn _ ha hb hb').congr (he β).symm, ?_⟩
    · intro x hx y hy hxy
      rw [he β hx, he β hy]
      exact Optimization.SecularResolvent.strictMonoOn_rpow_normSqResolvent
        hh hn _ ha hb' hx hy hxy
    · exact (Optimization.SecularResolvent.tendsto_rpow_neg_normSqResolvent_atTop
        hh hn _ ha hb').congr' (he' β).symm

/-- Corrected Lemma 8.2.3: positive powers have negative first and positive second
 derivative; negative powers in `[-1/2,0)` have positive first and nonpositive second
 derivative. Strict negative curvature is asserted only above the affine endpoint. -/
theorem lemma_8_2_3_corrected (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {β t : ℝ} (ht : secularThreshold hH hM < t) :
    (0 < β → deriv (transformedSecularFunction g H M β) t < 0 ∧
      0 < deriv (deriv (transformedSecularFunction g H M β)) t) ∧
    (β < 0 → 0 < deriv (transformedSecularFunction g H M β) t) ∧
    (-(1 / 2 : ℝ) ≤ β → β < 0 →
      deriv (deriv (transformedSecularFunction g H M β)) t ≤ 0) ∧
    (-(1 / 2 : ℝ) < β → β < 0 →
      deriv (deriv (transformedSecularFunction g H M β)) t < 0) := by
  have he : transformedSecularFunction g H M β =ᶠ[𝓝 t]
      (fun x => Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) x ^ β) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact transformedSecularFunction_eqOn hH hM β hx
  have hh := secularHessian_isSymmetric hH hM
  have hn := Optimization.SecularResolvent.toEnergy_inv_ne_zero
    hM.isPreconditioner_toEuclideanLin hg
  have ha := secular_admissible hH hM ht
  have hn' := fun i => ne_of_gt (ha i)
  have hd := Optimization.SecularResolvent.deriv_normSqResolvent_neg hh hn ha
  have hp := Real.rpow_pos_of_pos
    (Optimization.SecularResolvent.normSqResolvent_pos hh hn hn') (β - 1)
  rw [he.deriv_eq, he.deriv.deriv_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    refine ⟨?_, Optimization.SecularResolvent.deriv2_rpow_normSqResolvent_pos hh hn hb ha⟩
    rw [Optimization.SecularResolvent.deriv_rpow_normSqResolvent hh hn β hn']
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hd hb) hp
  · intro hb
    rw [Optimization.SecularResolvent.deriv_rpow_normSqResolvent hh hn β hn']
    exact mul_pos (mul_pos_of_neg_of_neg hd hb) hp
  · exact fun hb hb' =>
      Optimization.SecularResolvent.deriv2_rpow_normSqResolvent_nonpos hh hn hb hb' ha
  · exact fun hb hb' =>
      Optimization.SecularResolvent.deriv2_rpow_normSqResolvent_neg hh hn hb hb' ha

/-- Corrected Theorem 8.2.5: the tangent bounds always hold; strictness requires a nonzero
perturbation and, in the negative-power case, an exponent strictly greater than `-1/2`. -/
theorem theorem_8_2_5_corrected (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {β c δ : ℝ} (hc : secularThreshold hH hM < c)
    (hx : secularThreshold hH hM < c + δ) :
    (0 < β →
      transformedSecularFunction g H M β c +
        deriv (transformedSecularFunction g H M β) c * δ ≤
          transformedSecularFunction g H M β (c + δ)) ∧
    (-(1 / 2 : ℝ) ≤ β → β < 0 →
      transformedSecularFunction g H M β (c + δ) ≤
        transformedSecularFunction g H M β c +
          deriv (transformedSecularFunction g H M β) c * δ) ∧
    (δ ≠ 0 → 0 < β →
      transformedSecularFunction g H M β c +
        deriv (transformedSecularFunction g H M β) c * δ <
          transformedSecularFunction g H M β (c + δ)) ∧
    (δ ≠ 0 → -(1 / 2 : ℝ) < β → β < 0 →
      transformedSecularFunction g H M β (c + δ) <
        transformedSecularFunction g H M β c +
          deriv (transformedSecularFunction g H M β) c * δ) := by
  have hd := (contDiffAt_transformedSecularFunction hH hM hg β hc 1).differentiableAt
    (by norm_num)
  have hcor := corollary_8_2_4 hH hM hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    simpa only [add_sub_cancel_left] using
      ((hcor.1 β hb).2.1.convexOn.tangent_le hc hx hd)
  · intro hb hb'
    simpa only [add_sub_cancel_left] using
      ((hcor.2 β hb hb').2.1.le_tangent hc hx hd)
  · intro hδ hb
    simpa only [add_sub_cancel_left] using
      ((hcor.1 β hb).2.1.tangent_lt hc hx hd (by intro h; apply hδ; linarith))
  · intro hδ hb hb'
    have hs := Optimization.SecularResolvent.strictConcaveOn_rpow_normSqResolvent
      (secularHessian_isSymmetric hH hM)
      (Optimization.SecularResolvent.toEnergy_inv_ne_zero hM.isPreconditioner_toEuclideanLin hg)
      _ (secularThreshold_add_eigenvalue_nonneg hH hM) hb hb'
    have hs' := hs.congr (transformedSecularFunction_eqOn (g := g) hH hM β).symm
    simpa only [add_sub_cancel_left] using
      (hs'.lt_tangent hc hx hd (by intro h; apply hδ; linarith))

/-- Positive definiteness of the original shift excludes every generalized spectral pole,
including at negative shifts that still give a positive definite matrix. -/
theorem secular_nonsingular_of_posDef (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (hp : (H + t • M).PosDef) :
    ∀ i, t + secularEigenvalues hH hM i ≠ 0 := by
  intro i hi
  have hs : Matrix.toEuclideanLin (H + t • M) (secularEigenvector hH hM i) = 0 := by
    rw [toEuclideanLin_metric_shift]
    change Matrix.toEuclideanLin H (secularEigenvector hH hM i) +
      t • Matrix.toEuclideanLin M (secularEigenvector hH hM i) = 0
    rw [secularEigenvector_equation, ← add_smul]
    have hh : secularEigenvalues hH hM i + t = 0 := by linarith
    rw [hh, zero_smul]
  have hv : secularEigenvector hH hM i = 0 :=
    hp.isSymmetricCoercive_toEuclideanLin.isCoercive.injective
      (show Matrix.toEuclideanLin (H + t • M) (secularEigenvector hH hM i) =
        Matrix.toEuclideanLin (H + t • M) 0 by simpa only [map_zero] using hs)
  have he := congrArg hM.isPreconditioner_toEuclideanLin.toEnergy hv
  have hn := (secularHessian_isSymmetric hH hM).eigenvectorBasis rfl |>.toBasis.ne_zero i
  apply hn
  rw [OrthonormalBasis.coe_toBasis]
  simpa only [secularEigenvector, LinearEquiv.apply_symm_apply, map_zero] using he

/-- The source step is exactly the genuine metric inverse step. -/
theorem secularStep_eq_weightedResolventStep :
    secularStep g H M = weightedResolventStep
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap
      (Matrix.toEuclideanLin M) g := by
  funext t
  rw [secularStep, weightedResolventStep, toEuclideanLin_metric_shift]

/-- Theorem 8.2.6. All actual vector and scalar derivatives satisfy (8.2.27)–(8.2.30)
whenever the original shifted matrix is positive definite, including at negative shifts. -/
theorem theorem_8_2_6 (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (hp : (H + t • M).PosDef) :
    secularDerivativeCoefficient 0 = 1 ∧ ∀ k : ℕ,
      (iteratedDeriv (2 * k + 1) (secularData g H M) t =
        2 * secularDerivativeCoefficient k *
          inner ℝ (iteratedDeriv k (secularStep g H M) t)
            (Matrix.toEuclideanLin M (iteratedDeriv (k + 1) (secularStep g H M) t))) ∧
      (iteratedDeriv (2 * k + 2) (secularData g H M) t =
        secularDerivativeCoefficient (k + 1) *
          weightedNorm M (iteratedDeriv (k + 1) (secularStep g H M) t) ^ 2) ∧
      (Matrix.toEuclideanLin (H + t • M)
        (iteratedDeriv (k + 1) (secularStep g H M) t) =
          -((k + 1 : ℕ) : ℝ) • Matrix.toEuclideanLin M
            (iteratedDeriv k (secularStep g H M) t)) ∧
      (secularDerivativeCoefficient (k + 1) =
        2 * (2 * (k : ℝ) + 3) / (k + 1) * secularDerivativeCoefficient k) := by
  have hm := hM.isPreconditioner_toEuclideanLin
  have hh := hH.isSymmetric_toEuclideanLin
  have ht := secular_nonsingular_of_posDef hH hM hp
  have hπ : secularData g H M = weightedNormSqResolvent
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap
      (Matrix.toEuclideanLin M) g := funext fun x => secularData_eq_weightedResolvent x
  refine ⟨secularDerivativeCoefficient_zero, fun k => ?_⟩
  refine ⟨?_, ?_, ?_, secularDerivativeCoefficient_succ k⟩
  · simpa only [← hπ, ← secularStep_eq_weightedResolventStep] using
      iteratedDeriv_weightedNormSqResolvent_odd hm
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) hh g k ht
  · simpa only [← hπ, ← secularStep_eq_weightedResolventStep,
      weightedNorm_eq_energyNorm] using
      iteratedDeriv_weightedNormSqResolvent_even hm
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) hh g k ht
  · simpa only [← secularStep_eq_weightedResolventStep,
      ← toEuclideanLin_metric_shift] using
      shift_iteratedDeriv_weightedResolventStep hm
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) hh g k ht


end CartisGouldToint.Chapter08.Section02
