import Numlib.Optimization.QuadraticHardCase
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Chapter 8, Section 3: secular algorithms and complete minimizer families

The full generalized eigenspace parametrizes the hard case, including repeated eigenvalues.
Particular solutions minimize the actual SPD metric norm. The corrected trust-region statement
retains interior kernel completions at multiplier zero.
-/

noncomputable section
open scoped InnerProductSpace
open Set
open Optimization.QuadraticSubproblem
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter08.Section03
variable {n : ℕ} {g s : EuclideanSpace ℝ (Fin n)}
  {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The shifted generalized eigenspace is exactly the nullspace of the shifted matrix. -/
theorem metric_shift_kernel_iff (lambda : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H z +
      lambda • Matrix.toEuclideanLin M z = 0 ↔
        Matrix.toEuclideanLin (H + lambda • M) z = 0 := by
  rw [toEuclideanLin_metric_shift]
  rfl

/-- The source regions on nonnegative shifts. `N` uses failure of strict positive definiteness,
so the endpoint zero is regular when `H` is positive definite. `L` includes the root endpoint.
The tuple lists `N`, `L`, `G`, and `F`. -/
def secularRegions (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (target : ℝ → ℝ) : Set ℝ × Set ℝ × Set ℝ × Set ℝ :=
  let N := {lambda | 0 ≤ lambda ∧ ¬ (H + lambda • M).PosDef}
  let L := {lambda | 0 ≤ lambda ∧ (H + lambda • M).PosDef ∧
    target lambda ≤ weightedNorm M (secularStep g H M lambda)}
  let G := {lambda | 0 ≤ lambda ∧ (H + lambda • M).PosDef ∧
    weightedNorm M (secularStep g H M lambda) < target lambda}
  (N, L, G, L ∪ G)

/-- The regular set includes exactly the nonnegative strictly positive definite shifts. -/
@[simp] theorem mem_secularRegions_F (target : ℝ → ℝ) (lambda : ℝ) :
    lambda ∈ (secularRegions g H M target).2.2.2 ↔
      0 ≤ lambda ∧ (H + lambda • M).PosDef := by
  change ((0 ≤ lambda ∧ (H + lambda • M).PosDef ∧
      target lambda ≤ weightedNorm M (secularStep g H M lambda)) ∨
    (0 ≤ lambda ∧ (H + lambda • M).PosDef ∧
      weightedNorm M (secularStep g H M lambda) < target lambda)) ↔ _
  constructor
  · rintro (⟨hl, hp, _⟩ | ⟨hl, hp, _⟩) <;> exact ⟨hl, hp⟩
  · rintro ⟨hl, hp⟩
    rcases le_or_gt (target lambda) (weightedNorm M (secularStep g H M lambda)) with h | h
    · exact Or.inl ⟨hl, hp, h⟩
    · exact Or.inr ⟨hl, hp, h⟩

/-- A shifted null vector is a generalized eigenvector of eigenvalue `-lambda`. -/
theorem metric_shift_kernel_eigenvector_iff (lambda : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (H + lambda • M) z = 0 ↔
      Matrix.toEuclideanLin H z = (-lambda) • Matrix.toEuclideanLin M z := by
  rw [← metric_shift_kernel_iff]
  simp only [neg_smul, eq_neg_iff_add_eq_zero]
  rfl

/-- Under a positive semidefinite shift, `-lambda` bounds every generalized eigenvalue below.
Consequently every nonzero shifted null vector lies in the full lowest eigenspace. -/
theorem generalized_eigenvalue_lower_bound (hM : M.PosDef) {lambda mu : ℝ}
    (hp : (H + lambda • M).PosSemidef) {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    (he : Matrix.toEuclideanLin H v = mu • Matrix.toEuclideanLin M v) : -lambda ≤ mu := by
  have hp' := (Matrix.isPositive_toEuclideanLin_iff (A := H + lambda • M)).mpr hp
  have h := hp'.inner_nonneg_right v
  rw [toEuclideanLin_metric_shift] at h
  change 0 ≤ inner ℝ v (Matrix.toEuclideanLin H v + lambda • Matrix.toEuclideanLin M v) at h
  rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right] at h
  have hmv := hM.isSymmetricCoercive_toEuclideanLin.isCoercive.inner_self_pos hv
  simp only [RCLike.re_to_real, real_inner_comm] at hmv
  nlinarith

/-- The finite Taylor polynomial uses the queried derivatives, including the function value. -/
def secularTaylor (d : ℕ → ℝ) (degree : ℕ) (delta : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (degree + 1), d j * delta ^ j / j.factorial

/-- Actual derivative queries make the query polynomial exactly the earlier source Taylor
polynomial; algorithms therefore reuse the Taylor model from Section 8.2. -/
theorem secularTaylor_eq_of_queries (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (d : ℕ → ℝ) (degree : ℕ) (c delta : ℝ)
    (hd : ∀ j ≤ degree, d j = iteratedDeriv j (secularData g H M) c) :
    secularTaylor d degree delta =
      CartisGouldToint.Chapter08.Section02.secularTaylor g H M degree c delta := by
  unfold secularTaylor CartisGouldToint.Chapter08.Section02.secularTaylor
  apply Finset.sum_congr rfl
  intro j hj
  rw [hd j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)]

/-- Newton correction for the correctly transformed regularization equation. The target has
exponent `2 * beta / (r - 2)` because the secular data are a squared norm. -/
def regularizationNewtonCorrection (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (sigma r beta c : ℝ) : ℝ :=
  let f := fun x => secularData g H M x ^ beta - (x / sigma) ^ (2 * beta / (r - 2));
  -(f c) / deriv f c

/-- A run computes actual derivative queries, rightmost admissible odd Taylor roots, and the
largest of all Taylor and optional Newton candidates. After the tolerance test succeeds, its
trace is constant. The nonempty Taylor family handles `jMax = 0` without an empty maximum.
Only the initial shift is required to lie in `L`. Preservation of that region is a separate
property, unproved here. Its candidates never query a desired minimizer. -/
def algorithm_8_3_1 (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (sigma r epsilon initial : ℝ)
    (iMax jMax : ℕ) (beta : Fin jMax → ℝ) (trace : ℕ → ℝ)
    (query : ℕ → ℕ → ℝ) (taylor : ℕ → Fin iMax → ℝ) : Prop :=
  0 < sigma ∧ 2 < r ∧ 0 < epsilon ∧ 1 ≤ iMax ∧ trace 0 = initial ∧
    initial ∈ (secularRegions g H M (fun x => (x / sigma) ^ (1 / (r - 2)))).2.1 ∧
    (∀ j, beta j ∈ Icc (-1 / 2) ((r - 2) / 2) ∧ beta j ≠ 0) ∧
    ∀ k, (∀ j < k, epsilon < |trace (j + 1) - trace j|) →
      let c := trace k
      (∀ m ≤ 2 * iMax - 1, query k m = iteratedDeriv m (secularData g H M) c) ∧
      (∀ i, IsGreatest {d : ℝ | 0 ≤ c + d ∧ (H + (c + d) • M).PosDef ∧
        secularTaylor (query k) (2 * (i.val + 1) - 1) d =
          ((c + d) / sigma) ^ (2 / (r - 2))} (taylor k i - c)) ∧
      (∀ j, deriv (fun x => secularData g H M x ^ beta j -
        (x / sigma) ^ (2 * beta j / (r - 2))) c ≠ 0) ∧
      IsGreatest (range (taylor k) ∪ range (fun j =>
        c + regularizationNewtonCorrection g H M sigma r (beta j) c)) (trace (k + 1)) ∧
      (|trace (k + 1) - c| ≤ epsilon → ∀ l, k + 1 ≤ l → trace l = trace (k + 1))

/-- The trust-region specialization uses the explicit `beta = -1/2` Newton correction,
Taylor roots with right hand side `delta²`, actual derivative queries, the largest candidate,
and the same stopping recurrence as Algorithm 8.3.1. -/
def algorithm_8_3_2 (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (delta epsilon initial : ℝ)
    (iMax : ℕ) (trace : ℕ → ℝ) (query : ℕ → ℕ → ℝ)
    (taylor : ℕ → Fin iMax → ℝ) : Prop :=
  0 < delta ∧ 0 < epsilon ∧ 1 ≤ iMax ∧ trace 0 = initial ∧
    initial ∈ (secularRegions g H M (fun _ => delta)).2.1 ∧
    ∀ k, (∀ j < k, epsilon < |trace (j + 1) - trace j|) →
      let c := trace k
      (∀ m ≤ 2 * iMax - 1, query k m = iteratedDeriv m (secularData g H M) c) ∧
      (∀ i, IsGreatest {d : ℝ | 0 ≤ c + d ∧ (H + (c + d) • M).PosDef ∧
        secularTaylor (query k) (2 * (i.val + 1) - 1) d = delta ^ 2} (taylor k i - c)) ∧
      query k 1 ≠ 0 ∧
      IsGreatest (range (taylor k) ∪ {c + (2 * query k 0 / query k 1) *
        (1 - weightedNorm M (secularStep g H M c) / delta)}) (trace (k + 1)) ∧
      (|trace (k + 1) - c| ≤ epsilon → ∀ l, k + 1 ≤ l → trace l = trace (k + 1))

/-- Corollary 8.3.1, with the entire generalized eigenspace for repeated eigenvalues.
The first system singles out the unique minimum metric norm particular solution. Every global
minimizer is obtained by completing it in the full shifted kernel to the specified sphere.
Strict positive definiteness gives the easy-case uniqueness clause. -/
theorem corollary_8_3_1 (hH : H.IsSymm) (hM : M.PosDef) {sigma r : ℝ}
    (hsigma : 0 < sigma) (hr : 2 < r) (hs : regularizedMinimizer g H M sigma r s) :
    let lambda := sigma * weightedNorm M s ^ (r - 2)
    0 ≤ lambda ∧ (H + lambda • M).PosSemidef ∧
    (∃ ss : EuclideanSpace ℝ (Fin n),
      Matrix.toEuclideanLin (H + lambda • M) ss = -g ∧
      (∀ t, regularizedMinimizer g H M sigma r t ↔
        ∃ z : EuclideanSpace ℝ (Fin n), Matrix.toEuclideanLin (H + lambda • M) z = 0 ∧
          t = ss + z ∧ weightedNorm M t = (lambda / sigma) ^ (1 / (r - 2))) ∧
      (∀ t, Matrix.toEuclideanLin (H + lambda • M) t = -g →
        weightedNorm M ss ≤ weightedNorm M t ∧ (weightedNorm M ss = weightedNorm M t ↔ ss = t)) ∧
      regularizedModel g H M sigma r s =
        (1 / 2 : ℝ) * (inner ℝ g ss - (r - 2) / r * lambda *
          (lambda / sigma) ^ (2 / (r - 2)))) ∧
    ((H + lambda • M).PosDef → ∀ t, regularizedMinimizer g H M sigma r t → t = s) := by
  dsimp only
  have hp := (theorem_8_2_8 hH hM hsigma hr).1.mp hs
  obtain ⟨lambda, rfl, _, hp⟩ := hp
  refine ⟨mul_nonneg hsigma.le (Real.rpow_nonneg (Real.sqrt_nonneg _) _), hp, ?_, ?_⟩
  · have hh := weighted_power_minimizers_kernel_completion hM.isPreconditioner_toEuclideanLin
      hH.isSymmetric_toEuclideanLin hsigma hr
      (show IsMinOn (weightedPowerQuadratic g
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) (Matrix.toEuclideanLin M) sigma r)
        univ s by
          simpa only [regularizedMinimizer, regularizedModel_eq_weightedPowerQuadratic] using hs)
    simpa only [weightedNorm_eq_energyNorm, metric_shift_stationary_iff,
      metric_shift_kernel_iff,
      regularizedMinimizer, regularizedModel_eq_weightedPowerQuadratic] using hh
  · intro hp t ht
    exact (theorem_8_2_8 hH hM hsigma hr).2 hp hs t ht

/-- Corrected Corollary 8.3.2. The zero-multiplier case is the entire feasible kernel ball;
positive multipliers require the boundary sphere. Both cases include every minimizer and their
common minimum value, and the strictly positive definite case has a unique minimizer. -/
theorem corollary_8_3_2_corrected (hH : H.IsSymm) (hM : M.PosDef) {delta : ℝ}
    (hdelta : 0 < delta) (hs : trustRegionMinimizer g H M delta s) :
    ∃ lambda : ℝ, 0 ≤ lambda ∧ (H + lambda • M).PosSemidef ∧
      (∃ ss : EuclideanSpace ℝ (Fin n), Matrix.toEuclideanLin (H + lambda • M) ss = -g ∧
        (∀ t, trustRegionMinimizer g H M delta t ↔
          ∃ z : EuclideanSpace ℝ (Fin n), Matrix.toEuclideanLin (H + lambda • M) z = 0 ∧
            t = ss + z ∧ ((lambda = 0 ∧ weightedNorm M t ≤ delta) ∨
              (0 < lambda ∧ weightedNorm M t = delta))) ∧
        (∀ t, Matrix.toEuclideanLin (H + lambda • M) t = -g →
          weightedNorm M ss ≤ weightedNorm M t ∧
            (weightedNorm M ss = weightedNorm M t ↔ ss = t)) ∧
        quadraticModel g H s = (1 / 2 : ℝ) * (inner ℝ g ss - lambda * delta ^ 2)) ∧
      ((H + lambda • M).PosDef → ∀ t, trustRegionMinimizer g H M delta t → t = s) := by
  obtain ⟨hfeas, lambda, hl, hstat, hp, hc⟩ := (theorem_8_2_7 hH hM hdelta).1.mp hs
  refine ⟨lambda, hl, hp, ?_, ?_⟩
  · have hstat' :=
      (metric_shift_stationary_iff (g := g) (s := s) (H := H) (M := M) lambda).mpr hstat
    have hp' : ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap +
        lambda • Matrix.toEuclideanLin M).IsPositive := by
      rw [← toEuclideanLin_metric_shift, Matrix.isPositive_toEuclideanLin_iff]
      exact hp
    have hh := weighted_ball_minimizers_kernel_completion hM.isPreconditioner_toEuclideanLin
      hH.isSymmetric_toEuclideanLin (s := s) (delta := delta)
      (by simpa only [weightedNorm_eq_energyNorm] using hfeas)
      hl hstat' hp' (by simpa only [weightedNorm_eq_energyNorm] using hc)
    simpa only [metric_shift_stationary_iff, metric_shift_kernel_iff, trustRegionMinimizer,
      weightedNorm_eq_energyNorm, quadraticModel_eq_quadratic] using hh
  · intro hpd t ht
    exact (theorem_8_2_7 hH hM hdelta).2 lambda hs hl hstat hpd hc t ht

end CartisGouldToint.Chapter08.Section03
