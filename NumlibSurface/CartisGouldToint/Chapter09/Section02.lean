import Mathlib.Algebra.Order.Star.Real
import Numlib.Optimization.SecularPositiveDomain
import Numlib.Optimization.SafeguardedSecularSearchLimit
import Numlib.Optimization.SafeguardedSearchEndpoint
import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Chapter 9, Section 2: actual secular classification and safeguarded search

The classifier tests actual positive definiteness and the actual shifted solve. The complete
numbered algorithm records the optional eigenvalue estimates and all geometric/affine choices.
Spectral geometry proves the root-order certificates and interval invariants. Infinite histories
contract to the enclosed endpoint and reach every positive width stopping tolerance.
Finite entry requires careful endpoint treatment: a non-strict initial bracket can start at
the root as its lower endpoint and then approach that endpoint forever from above.
-/

noncomputable section
open Set Optimization.SafeguardedSecularSearch
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter09.Section02
variable {n : ℕ}

/-- Actual `N/L/G` classification by shifted positive definiteness and the secular norm. -/
def secularClassifier (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (target : ℝ → ℝ) (lambda : ℝ) : Region := by
  classical
  exact if (H + lambda • M).PosDef then
    if target lambda ≤ weightedNorm M (secularStep g H M lambda) then .lower else .greater
    else .negative

/-- Negative-region classification means precisely failure of strict positive definiteness. -/
@[simp] theorem secularClassifier_eq_negative (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) (lambda : ℝ) :
    secularClassifier g H M target lambda = .negative ↔ ¬(H + lambda • M).PosDef := by
  classical
  unfold secularClassifier
  split_ifs <;> simp_all

/-- Lower-side classification means a regular shift whose actual norm is above the target. -/
@[simp] theorem secularClassifier_eq_lower (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) (lambda : ℝ) :
    secularClassifier g H M target lambda = .lower ↔ (H + lambda • M).PosDef ∧
      target lambda ≤ weightedNorm M (secularStep g H M lambda) := by
  classical
  unfold secularClassifier
  split_ifs <;> simp_all

/-- Greater-side classification uses the strict actual-norm comparison. -/
@[simp] theorem secularClassifier_eq_greater (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) (lambda : ℝ) :
    secularClassifier g H M target lambda = .greater ↔ (H + lambda • M).PosDef ∧
      weightedNorm M (secularStep g H M lambda) < target lambda := by
  classical
  unfold secularClassifier
  split_ifs <;> simp_all

/-- The negative classifier is exactly the earlier source region at nonnegative shifts. -/
theorem secularClassifier_mem_N (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) {lambda : ℝ} (hl : 0 ≤ lambda) :
    secularClassifier g H M target lambda = .negative ↔
      lambda ∈ (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).1 := by
  simp [CartisGouldToint.Chapter08.Section03.secularRegions, hl]

/-- The lower classifier is exactly the earlier source lower region. -/
theorem secularClassifier_mem_L (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) {lambda : ℝ} (hl : 0 ≤ lambda) :
    secularClassifier g H M target lambda = .lower ↔
      lambda ∈ (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.1 := by
  simp [CartisGouldToint.Chapter08.Section03.secularRegions, hl]

/-- The greater classifier is exactly the earlier source greater region. -/
theorem secularClassifier_mem_G (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) {lambda : ℝ} (hl : 0 ≤ lambda) :
    secularClassifier g H M target lambda = .greater ↔
      lambda ∈ (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.2.1 := by
  simp [CartisGouldToint.Chapter08.Section03.secularRegions, hl]

/-- The operational search uses the actual source classifier, not a root-sign oracle. -/
def secularSearchExecution (p : Parameters) (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) (cutoff root : ℝ)
    (s : ℕ → State) (c : ℕ → Choice) : Prop :=
  IsRun p (secularClassifier g H M target) cutoff root s c

/-- Bracketing invariants follow from local classification certificates and the actual updates. -/
theorem secularSearchExecution.brackets {p : Parameters} {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} {target : ℝ → ℝ} {cutoff root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice}
    (h : secularSearchExecution p g H M target cutoff root s c)
    (hc : ClassifierSpec (secularClassifier g H M target) cutoff root) (hr : cutoff ≤ root)
    (k : ℕ) (hn : ∀ j < k, secularClassifier g H M target (s j).candidate ≠ .lower) :
    Brackets root (s k) := IsRun.brackets h hc hr k hn

/-- The source execution exposes exactly the canonical operational update relation. -/
@[simp] theorem secularSearchExecution_iff (p : Parameters) (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (target : ℝ → ℝ) (cutoff root : ℝ)
    (s : ℕ → State) (c : ℕ → Choice) :
    secularSearchExecution p g H M target cutoff root s c ↔
      IsRun p (secularClassifier g H M target) cutoff root s c := Iff.rfl

/-- Local root-order certificates and strict initialization give a first lower-side trial.
The classification certificate contains no entry, limit, or complexity conclusion. -/
theorem secularSearchExecution.exists_first_lower {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {target : ℝ → ℝ} {cutoff root : ℝ} {s : ℕ → State} {c : ℕ → Choice}
    (h : secularSearchExecution p g H M target cutoff root s c)
    (hc : ClassifierSpec (secularClassifier g H M target) cutoff root)
    (hp : cutoff < root) (hi : (s 0).lower < root) :
    ∃ k, secularClassifier g H M target (s k).candidate = .lower ∧
      (∀ j < k, secularClassifier g H M target (s j).candidate ≠ .lower) ∧
      Brackets root (s k) ∧ 0 ≤ (s k).candidate ∧ (s k).candidate ≤ root :=
  IsRun.exists_first_lower h hc hp hi

/-- The endpoint test data have scalar Hessian and metric one, with gradient two. -/
def endpointGradient : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 2)

/-- Every nonnegative shift of the scalar endpoint test Hessian is strictly positive definite. -/
theorem endpoint_shift_posDef {lambda : ℝ} (hl : 0 ≤ lambda) :
    ((1 : Matrix (Fin 1) (Fin 1) ℝ) + lambda • 1).PosDef := by
  have he : (1 : Matrix (Fin 1) (Fin 1) ℝ) + lambda • 1 =
      Matrix.diagonal (fun _ => 1 + lambda) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [he]
  exact Matrix.posDef_diagonal_iff.mpr (fun _ => by linarith)

/-- The endpoint test uses its genuine shifted linear solve. -/
theorem endpoint_secularStep {lambda : ℝ} (hl : 0 ≤ lambda) :
    secularStep endpointGradient 1 1 lambda =
      WithLp.toLp 2 (fun _ : Fin 1 => -2 / (1 + lambda)) := by
  rw [secularStep, (Matrix.ringInverse_toEuclideanLin (endpoint_shift_posDef hl).isUnit).2]
  ext i
  simp [Matrix.inv_subsingleton, endpointGradient,
    Ring.inverse_eq_inv', div_eq_mul_inv, mul_comm]

/-- Its actual metric norm equals the elementary scalar secular norm. -/
theorem endpoint_secularNorm {lambda : ℝ} (hl : 0 ≤ lambda) :
    weightedNorm 1 (secularStep endpointGradient 1 1 lambda) = 2 / (1 + lambda) := by
  rw [endpoint_secularStep hl]
  suffices hs : Real.sqrt ((2 / (1 + lambda)) ^ 2) = 2 / (1 + lambda) by
    simpa [weightedNorm, Real.sqrt_sq, EuclideanSpace.norm_eq, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 1 + lambda by linarith)] using hs
  exact Real.sqrt_sq (by positivity)

/-- The actual scalar secular equation has the claimed unique nonnegative root. -/
theorem endpoint_secularRoot_iff {lambda : ℝ} (hl : 0 ≤ lambda) :
    weightedNorm 1 (secularStep endpointGradient 1 1 lambda) = 1 ↔ lambda = 1 := by
  rw [endpoint_secularNorm hl, div_eq_iff (show 1 + lambda ≠ 0 by linarith)]
  constructor <;> intro h <;> linarith

/-- The endpoint test's true classifier satisfies all local root-order certificates. -/
theorem endpoint_classifierSpec (cutoff : ℝ) :
    ClassifierSpec (secularClassifier endpointGradient 1 1 (fun _ => 1)) cutoff 1 := by
  constructor
  · intro lambda hl hc
    exact ((secularClassifier_eq_negative _ _ _ _ _).mp hc (endpoint_shift_posDef hl)).elim
  · intro lambda hl hc
    have hn := ((secularClassifier_eq_lower _ _ _ _ _).mp hc).2
    rw [endpoint_secularNorm hl] at hn
    have hh := (le_div_iff₀ (show 0 < 1 + lambda by linarith)).mp hn
    linarith
  · intro lambda hl hc
    have hn := ((secularClassifier_eq_greater _ _ _ _ _).mp hc).2
    rw [endpoint_secularNorm hl] at hn
    have hh := (div_lt_one (show 0 < 1 + lambda by linarith)).mp hn
    linarith

/-- Every actual trial in the infinite endpoint run lies on the greater side. -/
theorem endpoint_secularClassifier (k : ℕ) :
    secularClassifier endpointGradient 1 1 (fun _ => 1) (endpointState k).candidate = .greater := by
  apply (secularClassifier_eq_greater _ _ _ _ _).mpr
  have hpos : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  have hl : 0 ≤ (endpointState k).candidate := by rw [endpointState_candidate]; positivity
  refine ⟨endpoint_shift_posDef hl, ?_⟩
  rw [endpoint_secularNorm hl]
  apply (div_lt_one (by rw [endpointState_candidate]; positivity)).mpr
  change 2 < 1 + (1 + (1 / 2 : ℝ) ^ (k + 1))
  linarith

/-- A complete lawful run of the actual one-dimensional secular search never enters `L`,
despite a nonempty `L` and valid initial bounds. The lower bound is exactly the root. -/
theorem secular_endpoint_nontermination (cutoff : ℝ) :
    secularClassifier endpointGradient 1 1 (fun _ => 1) 1 = .lower ∧
      secularSearchExecution halfParameters endpointGradient 1 1 (fun _ => 1) cutoff 1
        endpointState (fun _ => halfChoice) ∧
      ∀ k, secularClassifier endpointGradient 1 1 (fun _ => 1) (endpointState k).candidate ≠
        .lower := by
  refine ⟨?_, ?_, ?_⟩
  · apply (secularClassifier_eq_lower _ _ _ _ _).mpr
    refine ⟨endpoint_shift_posDef (by norm_num), ?_⟩
    rw [endpoint_secularNorm (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  · apply (endpointState_isRun cutoff).congr_trials
    intro k
    rw [endpointState_greater, endpoint_secularClassifier]
  · intro k
    rw [endpoint_secularClassifier]
    decide

/-- The generalized shifted eigenvalues of an actual positive definite matrix are positive. -/
theorem secular_positive_spectrum {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) {a : ℝ} (ha : (H + a • M).PosDef) (i) :
    0 < a + secularEigenvalues hH hM i := by
  have hv : secularEigenvector hH hM i ≠ 0 := by
    intro hz
    have hh := secularEigenvector_orthonormal hH hM i i
    rw [hz] at hh
    simp at hh
  have hp := ha.isSymmetricCoercive_toEuclideanLin.isCoercive.inner_self_pos hv
  rw [toEuclideanLin_metric_shift] at hp
  change 0 < inner ℝ
    (Matrix.toEuclideanLin H (secularEigenvector hH hM i) +
      a • Matrix.toEuclideanLin M (secularEigenvector hH hM i))
    (secularEigenvector hH hM i) at hp
  rw [secularEigenvector_equation, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, secularEigenvector_orthonormal] at hp
  simpa only [ite_true, mul_one, add_comm] using hp

/-- The cutoff is below every nonnegative positive definite shift, including zero. -/
theorem secularThreshold_le_of_posDef {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) {a : ℝ} (hn : 0 ≤ a)
    (ha : (H + a • M).PosDef) : secularThreshold hH hM ≤ a := by
  change (↑(Finset.univ.sup fun i =>
    (⟨max 0 (-secularEigenvalues hH hM i), le_max_left _ _⟩ : NNReal)) : ℝ) ≤ a
  change Finset.univ.sup (fun i =>
    (⟨max 0 (-secularEigenvalues hH hM i), le_max_left _ _⟩ : NNReal)) ≤ ⟨a, hn⟩
  apply Finset.sup_le_iff.mpr
  intro i _
  change max 0 (-secularEigenvalues hH hM i) ≤ a
  exact max_le hn (by linarith [secular_positive_spectrum hH hM ha i])

/-- A positive positive-definite shift lies strictly above the nonnegative cutoff. -/
theorem secularThreshold_lt_of_posDef {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) {a : ℝ} (hn : 0 < a)
    (ha : (H + a • M).PosDef) : secularThreshold hH hM < a := by
  change Finset.univ.sup (fun i =>
    (⟨max 0 (-secularEigenvalues hH hM i), le_max_left _ _⟩ : NNReal)) < ⟨a, hn.le⟩
  apply (Finset.sup_lt_iff (show (0 : NNReal) < ⟨a, hn.le⟩ from hn)).mpr
  intro i _
  change max 0 (-secularEigenvalues hH hM i) < a
  exact max_lt hn (by linarith [secular_positive_spectrum hH hM ha i])

/-- Every shift above the actual generalized spectral cutoff is positive definite. -/
theorem secular_posDef_of_threshold_lt {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) {a : ℝ} (ha : secularThreshold hH hM < a) :
    (H + a • M).PosDef := by
  have he := Optimization.SecularResolvent.isPositive_isUnit_shift
    (secularHessian_isSymmetric hH hM) (secular_admissible hH hM ha)
  have hp : (H + a • M).PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff, toEuclideanLin_metric_shift]
    exact (Optimization.QuadraticSubproblem.isPositive_energy_shift_iff
      hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin a).mp he.1
  apply hp.posDef_iff_isUnit.mpr
  have hu := Optimization.SecularResolvent.isUnit_metric_shift
    hM.isPreconditioner_toEuclideanLin
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) he.2
  rw [← toEuclideanLin_metric_shift] at hu
  exact (Matrix.isUnit_toLin_iff (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).mp hu

/-- The spectral identity also holds at a positive definite cutoff endpoint. -/
theorem secularData_eq_spectral_of_posDef {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hM : M.PosDef)
    {a : ℝ} (ha : (H + a • M).PosDef) :
    secularData g H M a = Optimization.SecularResolvent.spectralNormSq
      (secularEigenvalues hH hM)
      (fun i => inner ℝ (secularEigenvector hH hM i) g) a := by
  rw [secularData_eq_weightedResolvent,
    Optimization.SecularResolvent.weightedNormSqResolvent_eq
      hM.isPreconditioner_toEuclideanLin
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) g
      (Optimization.SecularResolvent.isUnit_shift (secularHessian_isSymmetric hH hM) a
        (secular_nonsingular_of_posDef hH hM ha)),
    Optimization.SecularResolvent.normSqResolvent_eq_spectralNormSq
      (secularHessian_isSymmetric hH hM) _ a (secular_nonsingular_of_posDef hH hM ha)]
  congr 1
  funext i
  exact secular_coordinate hH hM i

/-- The genuine step norm strictly decreases between any two positive definite shifts. -/
theorem secularNorm_lt_of_lt {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hM : M.PosDef)
    (hg : g ≠ 0) {a b : ℝ} (ha : (H + a • M).PosDef)
    (hb : (H + b • M).PosDef) (hab : a < b) :
    weightedNorm M (secularStep g H M b) < weightedNorm M (secularStep g H M a) := by
  have hγ : ∃ i, inner ℝ (secularEigenvector hH hM i) g ≠ 0 := by
    obtain ⟨i, hi⟩ := Optimization.SecularResolvent.exists_repr_ne_zero
      (secularHessian_isSymmetric hH hM)
      (Optimization.SecularResolvent.toEnergy_inv_ne_zero
        hM.isPreconditioner_toEuclideanLin hg)
    refine ⟨i, ?_⟩
    rw [← secular_coordinate hH hM i]
    exact hi
  have hs := Optimization.SecularResolvent.spectralNormSq_lt_of_lt
    (secularEigenvalues hH hM) (fun i => inner ℝ (secularEigenvector hH hM i) g)
    (secular_positive_spectrum hH hM ha) hab hγ
  rw [← secularData_eq_spectral_of_posDef hH hM ha,
    ← secularData_eq_spectral_of_posDef hH hM hb] at hs
  exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hs

/-- An actual regular secular root determines all classifier order certificates. The target
is nondecreasing and the right-hand side is nonzero, so the comparison follows from strict
spectral decrease, including a possible positive definite endpoint at zero. -/
theorem secularClassifier_spec_of_root {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hM : M.PosDef)
    (hg : g ≠ 0) {target : ℝ → ℝ} (ht : MonotoneOn target (Set.Ici 0))
    {root : ℝ} (hr : 0 ≤ root) (hp : (H + root • M).PosDef)
    (he : weightedNorm M (secularStep g H M root) = target root) :
    ClassifierSpec (secularClassifier g H M target) (secularThreshold hH hM) root := by
  constructor
  · intro a hn hc
    by_contra! hlt
    exact ((secularClassifier_eq_negative _ _ _ _ _).mp hc)
      (secular_posDef_of_threshold_lt hH hM hlt)
  · intro a hn hc
    obtain ⟨ha, hnorm⟩ := (secularClassifier_eq_lower _ _ _ _ _).mp hc
    by_contra! hlt
    have hs := secularNorm_lt_of_lt hH hM hg hp ha hlt
    have hm := ht hr hn hlt.le
    rw [he] at hs
    linarith
  · intro a hn hc
    obtain ⟨ha, hnorm⟩ := (secularClassifier_eq_greater _ _ _ _ _).mp hc
    by_contra! hlt
    have hs := secularNorm_lt_of_lt hH hM hg ha hp hlt
    have hm := ht hn hr hlt.le
    rw [he] at hs
    linarith

/-- When the lower region is empty, the spectral endpoint still supplies the full classifier
certificates. This case needs no totalized secular equation at a singular matrix. -/
theorem secularClassifier_spec_of_empty_lower {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hM : M.PosDef)
    (target : ℝ → ℝ)
    (hempty : (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.1 = ∅) :
    ClassifierSpec (secularClassifier g H M target)
      (secularThreshold hH hM) (secularThreshold hH hM) := by
  constructor
  · intro a hn hc
    by_contra! hlt
    exact ((secularClassifier_eq_negative _ _ _ _ _).mp hc)
      (secular_posDef_of_threshold_lt hH hM hlt)
  · intro a hn hc
    have hh := (secularClassifier_mem_L g H M target hn).mp hc
    rw [hempty] at hh
    exact hh.elim
  · intro a hn hc
    exact secularThreshold_le_of_posDef hH hM hn
      ((secularClassifier_eq_greater _ _ _ _ _).mp hc).1

/-- The optional source eigenvalue estimate is an upper bound on the actual least generalized
eigenvalue: equivalently, some generalized eigenvalue lies below the estimate. Using the
finite spectrum avoids choosing a spurious smallest eigenvalue in dimension zero. -/
def EigenvalueEstimate {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) (estimate : Option ℝ) : Prop :=
  ∀ e, estimate = some e → ∃ i, secularEigenvalues hH hM i ≤ e

/-- For a genuine least generalized eigenvalue, the optional estimate condition is exactly
the book's inequality `λ₁ ≤ λE`. -/
theorem eigenvalueEstimate_some_iff {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) {lambdaOne e : ℝ}
    (hmin : IsLeast (Set.range (secularEigenvalues hH hM)) lambdaOne) :
    EigenvalueEstimate hH hM (some e) ↔ lambdaOne ≤ e := by
  constructor
  · intro he
    obtain ⟨i, hi⟩ := he e rfl
    exact (hmin.2 (Set.mem_range_self i)).trans hi
  · intro he e' hh
    have heq : e = e' := Option.some.inj hh
    subst e'
    obtain ⟨i, hi⟩ := hmin.1
    exact ⟨i, hi.trans_le he⟩

/-- Negating an actual optional eigenvalue upper bound gives a valid cutoff lower bound. -/
theorem EigenvalueEstimate.below_threshold {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {estimate : Option ℝ}
    (he : EigenvalueEstimate hH hM estimate) :
    EstimateBelow (secularThreshold hH hM) (estimate.map Neg.neg) := by
  cases estimate with
  | none => exact estimateBelow_none _
  | some e =>
    apply (estimateBelow_some_iff (secularThreshold hH hM) (-e)).mpr
    obtain ⟨i, hi⟩ := he e rfl
    linarith [secularThreshold_add_eigenvalue_nonneg hH hM i]

/-- Algorithm 9.2.1, including its exact return rule. Each executed negative branch increases
the lower bound by the trial and optional `-λE` and selects one geometric/affine point. Each
 greater branch decreases the upper bound, applies the same optional spectral improvement,
 and selects a point in (9.2.2). `Choice.Legal` requires the ordered affine fractions and binary
 flags, and equates both endpoints in the negative branch. The separate optional estimate
 sequence records the actual `λE`, rather than assuming a root-bound certificate. Once the
 actual classifier detects `L`, the returned state is retained. Infinite legal histories are
 permitted: finite entry needs the strict initialization hypothesis in the theorem below;
 an empty `L` instead has the exact endpoint limit and width stopping guarantee. -/
structure algorithm_9_2_1 (p : Parameters) (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hM : M.PosDef)
    (target : ℝ → ℝ) (root : ℝ) (s : ℕ → State) (c : ℕ → Choice)
    (eigenEstimate : ℕ → Option ℝ) : Prop where
  /-- The source initialization encloses the root and the current nonnegative candidate. -/
  initial : Brackets root (s 0)
  /-- Every executed choice satisfies all ordered source safeguards. -/
  choice : ∀ k, (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
    (c k).Legal p (secularClassifier g H M target (s k).candidate)
  /-- The actual optional estimate satisfies `λE ≥ λ₁`. -/
  eigenvalue_estimate : ∀ k,
    (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
    EigenvalueEstimate hH hM (eigenEstimate k)
  /-- The lower-bound update uses the negative of the optional eigenvalue estimate. -/
  estimate_sign : ∀ k,
    (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
    (c k).estimate = (eigenEstimate k).map Neg.neg
  /-- Update the lower bound by the literal negative or greater branch. -/
  lower_update : ∀ k,
    (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
    (s (k + 1)).lower =
      (updateBounds (secularClassifier g H M target (s k).candidate) (s k) (c k).estimate).lower
  /-- Only the greater branch decreases the upper bound. -/
  upper_update : ∀ k,
    (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
    (s (k + 1)).upper =
      (updateBounds (secularClassifier g H M target (s k).candidate) (s k) (c k).estimate).upper
  /-- Select the next actual trial in the prescribed geometric/affine interval. -/
  candidate_update : ∀ k,
    (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
    let b := updateBounds (secularClassifier g H M target (s k).candidate) (s k) (c k).estimate
    (s (k + 1)).candidate ∈ Set.Icc (trial b (c k).thetaLower (c k).geometricLower)
      (trial b (c k).thetaUpper (c k).geometricUpper)
  /-- Exit with the actual lower-region candidate and retain the returned state. -/
  returned : ∀ k, secularClassifier g H M target (s k).candidate = .lower →
    ∀ j, k ≤ j → s j = s k

/-- The complete source algorithm is an actual operational secular search; its cutoff estimate
certificate is proved from the recorded eigenvalue estimate. -/
theorem algorithm_9_2_1.isRun {p : Parameters} {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} {hH : H.IsSymm} {hM : M.PosDef}
    {target : ℝ → ℝ} {root : ℝ} {s : ℕ → State} {c : ℕ → Choice}
    {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate) :
    secularSearchExecution p g H M target (secularThreshold hH hM) root s c := by
  refine ⟨h.initial, h.choice, ?_, h.lower_update, h.upper_update, h.candidate_update⟩
  intro k hn
  rw [h.estimate_sign k hn]
  exact (h.eigenvalue_estimate k hn).below_threshold

/-- In the negative branch the interval choice is exactly the single point prescribed by
the algorithm, rather than a relaxation to a larger interval. -/
theorem algorithm_9_2_1.negative_candidate {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ} {root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate)
    {k : ℕ} (hn : ∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower)
    (hc : secularClassifier g H M target (s k).candidate = .negative) :
    (s (k + 1)).candidate =
      trial (updateBounds .negative (s k) (c k).estimate) (c k).thetaLower
        (c k).geometricLower := by
  have he := (h.choice k hn).2.2.2.2 hc
  have hb := h.candidate_update k hn
  rw [hc, ← he.1, ← he.2] at hb
  exact le_antisymm hb.2 hb.1

/-- Actual spectral geometry, without an assumed classifier or convergence certificate,
 proves every pre-return interval invariant in the regular-root case. -/
theorem algorithm_9_2_1.brackets_of_root {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ} {root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate)
    (hg : g ≠ 0) (ht : MonotoneOn target (Set.Ici 0))
    (hp : (H + root • M).PosDef)
    (he : weightedNorm M (secularStep g H M root) = target root)
    (k : ℕ) (hn : ∀ j < k, secularClassifier g H M target (s j).candidate ≠ .lower) :
    Brackets root (s k) := by
  have hr : 0 ≤ root := h.initial.1.trans h.initial.2.1
  exact h.isRun.brackets (secularClassifier_spec_of_root hH hM hg ht hr hp he)
    (secularThreshold_le_of_posDef hH hM hr hp) k hn

/-- A regular secular root and a strictly smaller initial lower endpoint force a first
 return in the actual source region `L`; the returned history is constant thereafter. -/
theorem algorithm_9_2_1.exists_return_of_root {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ} {root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate)
    (hg : g ≠ 0) (ht : MonotoneOn target (Set.Ici 0))
    (hp : (H + root • M).PosDef)
    (he : weightedNorm M (secularStep g H M root) = target root)
    (hi : (s 0).lower < root) :
    ∃ k, (s k).candidate ∈
        (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.1 ∧
      (∀ j < k, secularClassifier g H M target (s j).candidate ≠ .lower) ∧
      Brackets root (s k) ∧ ∀ j, k ≤ j → s j = s k := by
  have hr : 0 < root := h.initial.1.trans_lt hi
  obtain ⟨k, hk, hfirst, hb, hn, _⟩ := h.isRun.exists_first_lower
    (secularClassifier_spec_of_root hH hM hg ht hr.le hp he)
    (secularThreshold_lt_of_posDef hH hM hr hp) hi
  exact ⟨k, (secularClassifier_mem_L g H M target hn).mp hk,
    hfirst, hb, h.returned k hk⟩

/-- In the empty-lower-region case the source algorithm preserves the actual spectral
 endpoint bracket at every iteration and never takes its lower-region return branch. -/
theorem algorithm_9_2_1.brackets_of_empty_lower {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target (secularThreshold hH hM) s c eigenEstimate)
    (hempty : (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.1 = ∅)
    (k : ℕ) : Brackets (secularThreshold hH hM) (s k) ∧
      secularClassifier g H M target (s k).candidate ≠ .lower := by
  have hc := secularClassifier_spec_of_empty_lower hH hM target hempty
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hb := h.isRun.brackets hc le_rfl k (fun j hj => (ih j hj).2)
    refine ⟨hb, ?_⟩
    intro hl
    have hh := (secularClassifier_mem_L g H M target
      (hb.1.trans hb.2.2.2.1)).mp hl
    rw [hempty] at hh
    exact hh.elim

/-- Empty `L` permits an infinite history. Its genuine bounds and trials converge to the
 spectral endpoint. Every positive width tolerance is eventually met, and the source's
 midpoint hard-case estimate then has error less than half that tolerance. This is an
 approximate stopping extension, not a claim that the base algorithm returns an exact root. -/
theorem algorithm_9_2_1.hard_case {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target (secularThreshold hH hM) s c eigenEstimate)
    (hempty : (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.1 = ∅) :
    (∀ k, secularClassifier g H M target (s k).candidate ≠ .lower) ∧
      Filter.Tendsto (fun k => (s k).lower) Filter.atTop (nhds (secularThreshold hH hM)) ∧
      Filter.Tendsto (fun k => (s k).upper) Filter.atTop (nhds (secularThreshold hH hM)) ∧
      Filter.Tendsto (fun k => (s k).candidate) Filter.atTop (nhds (secularThreshold hH hM)) ∧
      ∀ ε > 0, ∃ k, (s k).upper - (s k).lower < ε ∧
        |((s k).lower + (s k).upper) / 2 - secularThreshold hH hM| < ε / 2 := by
  have hc := secularClassifier_spec_of_empty_lower hH hM target hempty
  have hn (k : ℕ) : secularClassifier g H M target (s k).candidate ≠ .lower :=
    (h.brackets_of_empty_lower hempty k).2
  have ht := h.isRun.tendsto_bounds_candidate hc le_rfl hn
  refine ⟨hn, ht.1, ht.2.1, ht.2.2, ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ := ((h.isRun.tendsto_width hc le_rfl hn).eventually_lt_const hε).exists
  exact ⟨k, hk, (h.isRun.brackets hc le_rfl k (fun j _ => hn j)).midpoint_error_lt hk⟩

/-- An operational run with the actual spectral estimates and the source return rule is
 precisely a complete execution of Algorithm 9.2.1. -/
theorem algorithm_9_2_1.of_isRun {p : Parameters} {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} {hH : H.IsSymm} {hM : M.PosDef}
    {target : ℝ → ℝ} {root : ℝ} {s : ℕ → State} {c : ℕ → Choice}
    {eigenEstimate : ℕ → Option ℝ}
    (h : secularSearchExecution p g H M target (secularThreshold hH hM) root s c)
    (he : ∀ k, (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
      EigenvalueEstimate hH hM (eigenEstimate k))
    (hs : ∀ k, (∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower) →
      (c k).estimate = (eigenEstimate k).map Neg.neg)
    (hr : ∀ k, secularClassifier g H M target (s k).candidate = .lower →
      ∀ j, k ≤ j → s j = s k) :
    algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate :=
  ⟨h.initial, h.choice, he, hs, h.lower_update, h.upper_update, h.candidate_update, hr⟩

/-- The negative branch raises the lower endpoint by the actual trial and the optional
 negated eigenvalue estimate, and retains the upper endpoint. -/
theorem algorithm_9_2_1.negative_bounds {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ} {root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate)
    {k : ℕ} (hn : ∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower)
    (hc : secularClassifier g H M target (s k).candidate = .negative) :
    (s (k + 1)).lower = improveLower (max (s k).lower (s k).candidate)
        ((eigenEstimate k).map Neg.neg) ∧
      (s (k + 1)).upper = (s k).upper := by
  constructor
  · simpa only [hc, updateBounds_lower, ite_true, h.estimate_sign k hn]
      using h.lower_update k hn
  · simpa only [hc, updateBounds_upper, Region.negative, reduceCtorEq, ite_false]
      using h.upper_update k hn

/-- The greater branch retains or improves the lower endpoint using the same optional
 spectral estimate, and lowers the upper endpoint by the actual trial. -/
theorem algorithm_9_2_1.greater_bounds {p : Parameters}
    {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}
    {hH : H.IsSymm} {hM : M.PosDef} {target : ℝ → ℝ} {root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} {eigenEstimate : ℕ → Option ℝ}
    (h : algorithm_9_2_1 p g H M hH hM target root s c eigenEstimate)
    {k : ℕ} (hn : ∀ j ≤ k, secularClassifier g H M target (s j).candidate ≠ .lower)
    (hc : secularClassifier g H M target (s k).candidate = .greater) :
    (s (k + 1)).lower = improveLower (s k).lower ((eigenEstimate k).map Neg.neg) ∧
      (s (k + 1)).upper = min (s k).upper (s k).candidate := by
  constructor
  · simpa only [hc, updateBounds_lower, reduceCtorEq, ite_false, h.estimate_sign k hn]
      using h.lower_update k hn
  · simpa only [hc, updateBounds_upper, ite_true] using h.upper_update k hn

/-- The earlier endpoint history is a full execution of the numbered algorithm, with no
 optional eigenvalue estimates. Thus the need for strict lower initialization is not an
 artifact of a relaxed execution interface. Its `L` is nonempty but it never returns. -/
theorem endpoint_algorithm_9_2_1 :
    algorithm_9_2_1 halfParameters endpointGradient 1 1
      (by simp) (by simpa only [zero_smul, add_zero] using
        endpoint_shift_posDef (by norm_num : (0 : ℝ) ≤ 0)) (fun _ => 1) 1 endpointState
        (fun _ => halfChoice) (fun _ => none) ∧
      ∀ k, secularClassifier endpointGradient 1 1 (fun _ => 1)
        (endpointState k).candidate ≠ .lower := by
  have hn (k : ℕ) : secularClassifier endpointGradient 1 1 (fun _ => 1)
      (endpointState k).candidate ≠ .lower := by
    rw [endpoint_secularClassifier]
    exact Region.noConfusion
  refine ⟨algorithm_9_2_1.of_isRun ?_ ?_ ?_ ?_, hn⟩
  · apply (endpointState_isRun _).congr_trials
    intro k
    rw [endpointState_greater, endpoint_secularClassifier]
  · intro k _ e he
    cases he
  · intro k _
    rfl
  · intro k hk
    exact (hn k hk).elim

end CartisGouldToint.Chapter09.Section02
