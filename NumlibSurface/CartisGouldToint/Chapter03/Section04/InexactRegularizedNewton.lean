import Numlib.Optimization.InexactRegularizedNewton
import NumlibSurface.CartisGouldToint.Chapter03.Section01

/-!
# Inexact regularized Newton

The iRN framework uses the exact residual, slope and optional orthonormal-subspace curvature
conditions, cubic actual-decrease acceptance, and lower/upper interval resets and growth.
The curvature conclusion is confined to the final chosen subspace. The source's orthogonal
columns are represented by normalized orthogonal bases, so Q*Q = I as required by the
projected identity-shift formulas.
-/
noncomputable section
namespace CartisGouldToint.Chapter03.Section04
open Optimization Optimization.InexactRegularizedNewton
variable {n r : ℕ}

/-- Conditions (3.4.28)--(3.4.32): a feasible shifted Newton model step with both slope
bounds, the complete model-gradient residual bound, and optional projected model curvature.
A linear isometry represents the orthonormal columns of the chosen subspace basis. Zero
model steps are permitted for the second-order terminal test; executed trials are nonzero. -/
abbrev inexactRegularizedNewtonStep (p : Parameters) (second : Bool)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n))
    (lambda lower upper : ℝ)
    (Q : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  IsStep p second f x s lambda lower upper Q

/-- Algorithm 3.4.2. The Boolean `second = false` denotes the infinity sentinel. In the
second-order branch the final step is computed before testing curvature in its own subspace.
Only executed trials incur function evaluations; accepted successors refresh both derivatives. -/
abbrev algorithm_3_4_2 (p : Parameters) (second : Bool) (epsilon1 epsilon2 : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (lambda lower upper : ℕ → ℝ)
    (Q : ℕ → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (N : ℕ) : Prop :=
  IsRun p second epsilon1 epsilon2 f x s lambda lower upper Q N

variable {p : Parameters} {second : Bool} {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lambda lower upper : ℕ → ℝ}
  {Q : ℕ → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)} {N : ℕ}

/-- Lemma 3.4.7: a multiplier above the stated step-scaled threshold guarantees success. -/
theorem lemma_3_4_7 (h : TrialTrace p second f x s lambda lower upper Q N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) {k : ℕ} (hk : k < N)
    (hl : (2 * p.eta + p.kappa2 + L) * ‖s k‖ ≤ lambda k) :
    p.eta ≤ ratio f (x k) (s k) :=
  (h.step k hk).accepted_of_shift (h.nonzero k hk) hf.toHessianLipschitz hl

/-- Lemma 3.4.8: the upper regularization interval has the uniform bound (3.4.38). -/
theorem lemma_3_4_8 (h : TrialTrace p second f x s lambda lower upper Q N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) {k : ℕ} (hk : k ≤ N) :
    upper k ≤ max p.sigmaMax (p.gamma2 * (2 * p.eta + p.kappa2 + L)) :=
  h.upper_le hf.toHessianLipschitz hk

/-- Lemma 3.4.9: successful steps control the next gradient, and the optional second-order
step condition controls the current projected objective curvature. -/
theorem lemma_3_4_9 [NeZero r] (h : TrialTrace p second f x s lambda lower upper Q N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) {k : ℕ} (hk : k < N)
    (ha : p.eta ≤ ratio f (x k) (s k)) :
    2 * ‖gradient f (x (k + 1))‖ / (L + 4 * upperBound p L + 2 * p.kappa3) ≤ ‖s k‖ ^ 2 ∧
    (second = true → -projectedCurvature f (x k) (Q k) /
      (p.kappa4 + upperBound p L) ≤ ‖s k‖) :=
  ⟨h.accepted_step_sq hf.toHessianLipschitz hk ha,
    fun hs => h.curvature_step hf.toHessianLipschitz hs hk⟩

/-- Lemma 3.4.10: every contiguous block of unsuccessful iterations has at most the
logarithmic bound (3.4.42). This includes blocks between consecutive successful iterations. -/
theorem lemma_3_4_10 (h : TrialTrace p second f x s lambda lower upper Q N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) (a m : ℕ) (hN : a + m ≤ N)
    (ha : ∀ j < m, ¬p.eta ≤ ratio f (x (a + j)) (s (a + j))) :
    (m : ℝ) ≤ Real.log (upperBound p L / p.sigmaMin) / Real.log p.gamma1 + 1 :=
  h.failed_block_count hf.toHessianLipschitz a m hN ha

/-- Theorem 3.4.11: uniform constants give first-order termination, function evaluation
complexity and cached gradient/Hessian evaluation complexity of order epsilon1^(-3/2).
The hypothesis specifies only local laws on every still-required finite prefix. -/
theorem theorem_3_4_11 (p : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) {L low : ℝ} (hf : Section01.hessianLipschitz f L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧
      ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 →
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (lambda lower upper : ℕ → ℝ)
        (Q : ℕ → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
        x 0 = x0 →
        (∀ N, (∀ j < N, tolerance < ‖gradient f (x j)‖) →
          TrialTrace p false f x s lambda lower upper Q N) →
        ∃ K : ℕ, ‖gradient f (x K)‖ ≤ tolerance ∧
          (∀ j < K, tolerance < ‖gradient f (x j)‖) ∧
          (functionEvaluations K : ℝ) ≤ kA * ((f x0 - low) / tolerance ^ (3 / 2 : ℝ)) + kB ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kS * ((f x0 - low) / tolerance ^ (3 / 2 : ℝ)) + 2 :=
  exists_firstOrder_complexity_constants p f x0 hf.toHessianLipschitz hlow

/-- Theorem 3.4.12: iRN terminates with the gradient bound and curvature at least minus the
second tolerance in its final chosen subspace, with uniform function and derivative budgets
of order max(epsilon1^(-3/2), epsilon2^(-3)). The finite-prefix premise contains only actual
local algorithm laws; termination and both evaluation budgets are proved conclusions. -/
theorem theorem_3_4_12 [NeZero r] (p : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    {L low : ℝ} (hf : Section01.hessianLipschitz f L) (hlow : ∀ y, low ≤ f y) :
    ∃ kT kC kD : ℝ, 0 < kT ∧ 0 < kC ∧ 0 < kD ∧
      ∀ tolerance1 tolerance2 : ℝ, 0 < tolerance1 → tolerance1 ≤ 1 →
        0 < tolerance2 → tolerance2 ≤ 1 →
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (lambda lower upper : ℕ → ℝ)
        (Q : ℕ → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
        x 0 = x0 →
        (∀ N, (∀ j < N, ¬Stationary true f tolerance1 tolerance2 (x j) (Q j)) →
          SecondOrderPrefix p f x s lambda lower upper Q N) →
        ∃ K : ℕ, algorithm_3_4_2 p true tolerance1 tolerance2 f x s lambda lower upper Q K ∧
          (functionEvaluations K : ℝ) ≤
            kC * ((f x0 - low) / min (tolerance1 ^ (3 / 2 : ℝ)) (tolerance2 ^ 3)) + kD ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kT * ((f x0 - low) / min (tolerance1 ^ (3 / 2 : ℝ)) (tolerance2 ^ 3)) + 2 :=
  exists_secondOrder_complexity_constants p f x0 hf.toHessianLipschitz hlow

end CartisGouldToint.Chapter03.Section04
