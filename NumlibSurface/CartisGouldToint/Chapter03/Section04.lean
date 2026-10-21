import NumlibSurface.CartisGouldToint.Chapter03.Section04.InexactRegularizedNewton
import Numlib.Optimization.RegularizedTrustRegion
import NumlibSurface.CartisGouldToint.Chapter03.Section02

/-!
# Quadratically regularized trust regions

The TR-epsilon algorithm uses the true quadratic Taylor polynomial with a quadratic norm
regularizer, actual objective acceptance, and the original three radius-update intervals.
Finite executions record first termination and cache derivatives after rejected trials.
-/

noncomputable section
namespace CartisGouldToint.Chapter03.Section04
open Optimization Optimization.RegularizedTrustRegion
variable {n : ℕ}

/-- Algorithm 3.4.1. `second = false` denotes the infinity sentinel in the first-order branch;
`second = true` uses the actual full Euclidean Hessian curvature and forces a boundary step
whenever that curvature is below minus the second tolerance. The strict regularized-model
decrease and actual derivative residual are required only before the first stopping index. -/
abbrev algorithm_3_4_1 (p : TrustRegion.Parameters) (second : Bool)
    (theta epsilon epsilon1 epsilon2 : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (delta : ℕ → ℝ) (N : ℕ) : Prop :=
  IsRun p second theta epsilon epsilon1 epsilon2 f x s delta N

variable {p : TrustRegion.Parameters} {second : Bool} {theta epsilon epsilon1 epsilon2 : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {delta : ℕ → ℝ} {N : ℕ}

/-- Lemma 3.4.1: Taylor decrease pays for the quadratic regularizer. -/
theorem lemma_3_4_1 (h : algorithm_3_4_1 p second theta epsilon epsilon1 epsilon2 f x s delta N)
    {k : ℕ} (hk : k < N) :
    epsilon / 2 * ‖s k‖ ^ 2 ≤ Chapter01.Section03.taylorModel f 2 (x k) 0 -
      Chapter01.Section03.taylorModel f 2 (x k) (s k) :=
  h.toTrialTrace.predicted_decrease hk

/-- Lemma 3.4.2: small radii are very successful; every executed radius has the uniform lower
bound. The normalized f.HL bound includes `L ≥ 1`, as used in the printed proof. -/
theorem lemma_3_4_2 (h : algorithm_3_4_1 p second theta epsilon epsilon1 epsilon2 f x s delta N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) :
    (∀ k < N, delta k < 3 * (1 - p.eta2) / L * epsilon →
      p.eta2 ≤ ratio f (x k) (s k) ∧ delta k ≤ delta (k + 1)) ∧
    (∀ k ≤ N, ((1 - p.eta2) * p.gamma1 / L) * epsilon ≤ delta k) := by
  refine ⟨?_, fun k hk => h.toTrialTrace.radius_lower_normalized hf.toHessianLipschitz hf.one_le hk⟩
  intro k hk hsmall
  have hL : 0 < L := by linarith [hf.one_le]
  have hs : p.eta2 ≤ ratio f (x k) (s k) := by
    apply h.toTrialTrace.ratio_ge_of_radius hf.toHessianLipschitz hk
    have hh : delta k < (3 * (1 - p.eta2) * epsilon) / L := by
      convert hsmall using 1; ring
    have hh' := (lt_div_iff₀ hL).mp hh
    nlinarith only [hh']
  refine ⟨hs, ?_⟩
  have hu := h.update k hk
  rw [ite_eq_left hs] at hu
  exact hu.1

/-- Lemma 3.4.3: a successful strictly interior trial has the stated length lower bound.
The proof uses the correct quadratic inequality directly, avoiding the misplaced parentheses
and denominators in the supplied transcription of (3.4.11)--(3.4.12). -/
theorem lemma_3_4_3 (h : algorithm_3_4_1 p second theta epsilon epsilon1 epsilon2 f x s delta N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) {k : ℕ} (hk : k < N)
    (hs : p.eta1 ≤ ratio f (x k) (s k)) (hint : ‖s k‖ < delta k) :
    min epsilon (‖gradient f (x (k + 1))‖ / epsilon) /
      Real.sqrt (1 + 2 * (L + theta)) ≤ ‖s k‖ :=
  h.toTrialTrace.interior_step_lower hf.toHessianLipschitz hk hs hint

/-- Lemma 3.4.4: interior and boundary sufficient decrease, stated separately. The printed
proof interchanges its references to (3.4.13) and (3.4.14); the conclusions here follow their
actual interior and boundary hypotheses. -/
theorem lemma_3_4_4 (h : algorithm_3_4_1 p second theta epsilon epsilon1 epsilon2 f x s delta N)
    {L : ℝ} (hf : Section01.hessianLipschitz f L) {k : ℕ} (hk : k < N)
    (hs : p.eta1 ≤ ratio f (x k) (s k)) :
    (‖s k‖ < delta k → decreaseCoefficient p L theta *
      min (epsilon ^ 3) (‖gradient f (x (k + 1))‖ ^ 2 / epsilon) ≤
        f (x k) - f (x (k + 1))) ∧
    (‖s k‖ = delta k → decreaseCoefficient p L theta * epsilon ^ 3 ≤
      f (x k) - f (x (k + 1))) :=
  ⟨fun hint => h.toTrialTrace.interior_decrease hf.toHessianLipschitz hk hs hint,
    fun hb => h.toTrialTrace.boundary_decrease hf.toHessianLipschitz hf.one_le hk hs hb⟩

/-- An executable finite prefix of TR-epsilon, without assuming a successful stopping test.
This interface allows termination to be proved from the local trial laws. -/
abbrev trEpsilonPrefix (p : TrustRegion.Parameters) (theta epsilon : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (delta : ℕ → ℝ) (N : ℕ) : Prop := TrialTrace p theta epsilon f x s delta N

/-- Theorem 3.4.5: tolerance-independent constants give first-order termination and objective,
gradient and Hessian evaluation budgets. The hypothesis asks only for the algorithm's local
laws on every still-required prefix; termination and both budgets are conclusions. -/
theorem theorem_3_4_5 (p : TrustRegion.Parameters) (theta : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (delta0 : ℝ)
    {L low : ℝ} (htheta : 0 < theta) (hf : Section01.hessianLipschitz f L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB kC : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧ 0 < kC ∧
      ∀ epsilon1 : ℝ, 0 < epsilon1 → epsilon1 ≤ 1 →
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (delta : ℕ → ℝ),
        x 0 = x0 → delta 0 = delta0 →
        (∀ N, (∀ j < N, epsilon1 < ‖gradient f (x j)‖) →
          trEpsilonPrefix p theta (Real.sqrt epsilon1) f x s delta N) →
        ∃ K : ℕ, algorithm_3_4_1 p false theta (Real.sqrt epsilon1) epsilon1 0 f x s delta K ∧
          (functionEvaluations K : ℝ) ≤
            kA * ((f x0 - low) / epsilon1 ^ (3 / 2 : ℝ)) +
              kB * |Real.log epsilon1| + kC ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kS * ((f x0 - low) / epsilon1 ^ (3 / 2 : ℝ)) + 2 := by
  obtain ⟨kS, kA, kB, kC, hS, hA, hB, hC, h⟩ :=
    exists_firstOrder_complexity_constants p theta f x0 delta0 htheta
      hf.toHessianLipschitz hf.one_le hlow
  refine ⟨kS, kA, kB, kC, hS, hA, hB, hC, ?_⟩
  intro epsilon1 he he1 x s delta hx hd hprefix
  obtain ⟨K, hK, hfirst, hfun, hderiv⟩ := h epsilon1 he he1 x s delta hx hd hprefix
  refine ⟨K, ?_, hfun, hderiv⟩
  refine { toTrialTrace := hprefix K hfirst
           epsilon_le_one := ?_
           epsilon1_pos := he
           epsilon1_le_one := he1
           epsilon2_domain := by simp
           coupling := rfl
           boundary := by simp
           terminal := ⟨hK, by simp⟩
           first := ?_ }
  · exact (Real.sqrt_le_one).mpr he1
  · intro j hj hs
    exact (not_le_of_gt (hfirst j hj)) hs.1



/-- Finite TR-epsilon trials with the current full-Hessian curvature boundary condition,
without assuming that a stopping index exists. -/
abbrev trEpsilonJointPrefix (p : TrustRegion.Parameters) (theta epsilon2 : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (delta : ℕ → ℝ) (N : ℕ) : Prop := JointPrefix p theta epsilon2 f x s delta N

/-- Theorem 3.4.6: tolerance-independent positive constants bound objective and cached
first/second derivative evaluations before the first joint stopping test. Curvature is that of
the full Euclidean Hessian. The proof uses a curvature-credit potential to repair the printed
proof's current/successor curvature mismatch; the displayed existential bounds are unchanged.
The particular explicit constants asserted later in the printed proof are not needed here. -/
theorem theorem_3_4_6 (p : TrustRegion.Parameters) (theta : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (delta0 : ℝ)
    {L low : ℝ} (htheta : 0 < theta) (hf : Section01.hessianLipschitz f L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kC kD : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kC ∧ 0 < kD ∧
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → epsilon1 ≤ 1 →
        0 < epsilon2 → epsilon2 ≤ 1 →
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (delta : ℕ → ℝ),
        x 0 = x0 → delta 0 = delta0 →
        (∀ N, (∀ j < N, ¬Stationary true f epsilon1 epsilon2 (x j)) →
          trEpsilonJointPrefix p theta epsilon2 f x s delta N) →
        ∃ K : ℕ, algorithm_3_4_1 p true theta epsilon2 epsilon1 epsilon2 f x s delta K ∧
          (functionEvaluations K : ℝ) ≤
            kA * ((f x0 - low) / min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) +
              kD * |Real.log epsilon2| + kC ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kS * ((f x0 - low) / min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) + 1 := by
  obtain ⟨kS, kA, kC, kD, hS, hA, hC, hD, h⟩ :=
    exists_joint_complexity_constants p theta f x0 delta0 htheta
      hf.toHessianLipschitz hf.one_le hlow
  refine ⟨kS, kA, kC, kD, hS, hA, hC, hD, ?_⟩
  intro epsilon1 epsilon2 he1 he11 he2 he21 x s delta hx hd hprefix
  obtain ⟨K, hK, hfirst, hfun, hderiv⟩ := h epsilon1 epsilon2 he1 he2 he21
    x s delta hx hd hprefix
  refine ⟨K, ?_, hfun, hderiv⟩
  exact { toTrialTrace := (hprefix K hfirst).toTrialTrace
          epsilon_le_one := he21
          epsilon1_pos := he1
          epsilon1_le_one := he11
          epsilon2_domain := fun _ => ⟨he2, he21⟩
          coupling := rfl
          boundary := fun _ => (hprefix K hfirst).boundary
          terminal := hK
          first := hfirst }

end CartisGouldToint.Chapter03.Section04
