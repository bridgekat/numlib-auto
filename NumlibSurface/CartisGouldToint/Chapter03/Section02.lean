import Numlib.Optimization.TrustRegionHessianSharpness
import Numlib.Optimization.TrustRegionSecondOrderSharpness
import Numlib.Optimization.TrustRegionSecondOrder
import NumlibSurface.CartisGouldToint.Chapter03.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section03

/-!
# Trust regions using exact second derivatives

TR2 specializes the first-order trust-region framework to the actual Hessian and optionally
requires eigenpoint decrease. The joint test uses approximate second-order conditions;
nonnegative curvature is not required for termination. Oracle costs count the initial
objective, gradient and Hessian evaluations, then every trial objective and accepted derivatives.
-/
noncomputable section
namespace CartisGouldToint.Chapter03.Section02
open Optimization Optimization.TrustRegionSecondOrder
open Optimization.QuadraticSubproblem
variable {n : ℕ}

/-- Assumption f.HBa: continuous second derivatives with a normalized uniform Hessian bound. -/
def hessianBound (f : EuclideanSpace ℝ (Fin n) → ℝ) (B : ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ 1 ≤ B ∧ ∀ y, ‖hessianOperator f y‖ ≤ B

/-- The eigenpoint (3.2.5), using an actual signed minimum-eigenvalue unit vector when its
curvature is negative and zero otherwise. -/
abbrev eigenpoint [NeZero n] {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (delta : ℝ) :
    EuclideanSpace ℝ (Fin n) := Optimization.TrustRegionSecondOrder.eigenpoint hf delta

/-- Algorithm 3.2.1: true quadratic Taylor model, feasible Cauchy decrease, optional eigenpoint
decrease, actual objective acceptance, and the three legal radius-update intervals.
The Boolean replaces the printed infinity sentinel; theorems specify the first stopping test. -/
abbrev algorithm_3_2_1 (p : TrustRegion.Parameters) (second : Bool)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (delta : ℕ → ℝ) : Prop := Optimization.TrustRegionSecondOrder.IsRun p second f x s delta

/-- The true Hessian model is exactly the earlier chapter's Taylor model. -/
theorem quadraticModel_eq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) :
    Chapter01.Section03.taylorModel f 2 x s =
      f x + quadratic (gradient f x) (hessianOperator f x) s :=
  taylorModel_eq f x s

/-- Bounded Hessians imply the earlier chapter's Lipschitz-gradient assumption. -/
theorem hessianBound.gradientLipschitz {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hf : hessianBound f B) : Chapter02.Section01.assumption_f_gL f B :=
  ⟨hf.1.of_le (by norm_num), hf.2.1, gradient_lipschitz_of_hessian_bound hf.1 hf.2.2⟩

variable {p : TrustRegion.Parameters} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {delta : ℕ → ℝ}

/-- Theorem 3.2.1: with the second-order test disabled, the first-order trust-region bound
applies unchanged. Accepted derivatives are cached, so the gradient and Hessian share a budget. -/
theorem theorem_3_2_1 (h : algorithm_3_2_1 p false f x s delta) {B low : ℝ}
    (hf : hessianBound f B) (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB kC : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧ 0 < kC ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
        Chapter02.Section01.approximateFirstOrderMinimizer f epsilon (x K) ∧
        (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
        (K : ℝ) + 1 ≤ kA * ((f (x 0) - low) / epsilon ^ 2) +
          kB * |Real.log epsilon| + kC ∧
        (ParameterUpdates.successCount
          (fun k => p.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
            (hessianOperator f (x k)) (x k) (s k)) K : ℝ) + 1 ≤
          kS * ((f (x 0) - low) / epsilon ^ 2) + 1 := by
  apply Chapter02.Section03.theorem_2_3_7
    ⟨h.toIsRun, fun k => bilinearOperator_isSymmetric (hessian_symmetric (hf.1.contDiffAt))⟩
    hf.gradientLipschitz ⟨by linarith [hf.2.1], fun k => hf.2.2 (x k)⟩ hlow

/-- Lemma 3.2.3: true eigenpoint decrease bounds the model reduction by half the magnitude
of the least Hessian eigenvalue times the square of the radius. -/
theorem lemma_3_2_3 [NeZero n] (h : algorithm_3_2_1 p true f x s delta)
    (k : ℕ)
    (hl : Chapter01.Section03.leastHessianEigenvalue f (x k) < 0) :
    (1 / 2 : ℝ) * |Chapter01.Section03.leastHessianEigenvalue f (x k)| * delta k ^ 2 ≤
      Chapter01.Section03.taylorModel f 2 (x k) 0 -
        Chapter01.Section03.taylorModel f 2 (x k) (s k) := by
  simpa only [quadraticModel_eq, add_sub_add_left_eq_sub,
    Chapter01.Section03.leastHessianEigenvalue, curvature] using h.curvature_decrease k hl

/-- Lemma 3.2.4: a radius below the cubic-remainder threshold is very successful and cannot
contract. The multiplicative threshold also gives the limiting case of a constant Hessian. -/
theorem lemma_3_2_4 [NeZero n] (h : algorithm_3_2_1 p true f x s delta) {L : ℝ}
    (hf : Section01.hessianLipschitz f L) (k : ℕ)
    (hl : Chapter01.Section03.leastHessianEigenvalue f (x k) < 0)
    (hsmall : delta k < 3 * (1 - p.eta2) *
      |Chapter01.Section03.leastHessianEigenvalue f (x k)| / L) :
    p.eta2 ≤ TrustRegion.ratio f (gradient f (x k)) (hessianOperator f (x k)) (x k) (s k) ∧
      delta k ≤ delta (k + 1) := by
  have hr := h.ratio_ge_of_curvature_radius hf.toHessianLipschitz k hl
    (by simpa only [mul_comm L, curvature, Chapter01.Section03.leastHessianEigenvalue]
      using ((lt_div_iff₀ (by linarith [hf.one_le] : 0 < L)).mp hsmall).le)
  have hu := h.toIsRun.update k
  rw [ite_eq_left hr] at hu
  exact ⟨hr, hu.1⟩

/-- Lemma 3.2.5: a tolerance-independent radius coefficient bounds every pretermination
prefix, including its endpoint. The first tolerance can be any positive real number. -/
theorem lemma_3_2_5 [NeZero n] (h : algorithm_3_2_1 p true f x s delta) {B L : ℝ}
    (hf : hessianBound f B) (hL : Section01.hessianLipschitz f L) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ epsilon1 epsilon2 : ℝ,
      0 < epsilon1 → 0 < epsilon2 → epsilon2 ≤ 1 → ∀ N : ℕ,
      (∀ j < N, ¬Stationary f epsilon1 epsilon2 (x j)) → ∀ k ≤ N,
        c * min epsilon1 epsilon2 ≤ delta k := by
  let c := jointRadiusCoefficient p B L (delta 0)
  obtain ⟨hc, _, hcd, hca, hcb⟩ :=
    jointRadiusCoefficient_spec p hf.2.1 hL.nonneg (h.toIsRun.radius_pos 0)
  refine ⟨c, hc, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  · intro epsilon1 epsilon2 he1 he2 he2one N ht k hk
    apply h.radius_lower_before_joint_test hL.toHessianLipschitz hf.2.1 hf.2.2 he1 he2
      ((mul_le_of_le_one_right hc.le ((min_le_right _ _).trans he2one)).trans hcd) hca hcb
    exact fun j hj => ht j (lt_of_lt_of_le hj hk)

/-- Theorem 3.2.6: the first approximate second-order stationary iterate has the printed mixed
power function budget and a common cached gradient/Hessian budget. Constants are chosen before
the tolerances. The logarithmic term uses the minimum of the two tolerances. -/
theorem theorem_3_2_6 [NeZero n] (h : algorithm_3_2_1 p true f x s delta) {B L low : ℝ}
    (hf : hessianBound f B) (hL : Section01.hessianLipschitz f L) (hlow : ∀ y, low ≤ f y) :
    ∃ kT kD kE kF : ℝ, 0 < kT ∧ 0 < kD ∧ 0 < kE ∧ 0 < kF ∧
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 → 0 < epsilon2 → epsilon2 ≤ 1 →
      ∃ K : ℕ,
        (‖gradient f (x K)‖ ≤ epsilon1 ∧
          -epsilon2 ≤ Chapter01.Section03.leastHessianEigenvalue f (x K)) ∧
        (∀ j < K, ¬Stationary f epsilon1 epsilon2 (x j)) ∧
        (K : ℝ) + 1 ≤ kD * ((f (x 0) - low) /
          min (epsilon1 ^ 2 * epsilon2) (epsilon2 ^ 3)) +
          kE * |Real.log (min epsilon1 epsilon2)| + kF ∧
        (ParameterUpdates.successCount
          (fun k => p.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
            (hessianOperator f (x k)) (x k) (s k)) K : ℝ) + 1 ≤
          kT * ((f (x 0) - low) / min (epsilon1 ^ 2 * epsilon2) (epsilon2 ^ 3)) + 1 := by
  obtain ⟨kT, kD, kE, kF, hT, hD, hE, hF, hs⟩ :=
    h.exists_joint_complexity_constants hL.toHessianLipschitz hf.2.1 hf.2.2 hlow
  refine ⟨kT, kD, kE, kF, hT, hD, hE, hF, ?_⟩
  intro epsilon1 epsilon2 he1 he2 he2one
  simpa only [accuracyScale_eq he1.le he2.le, Stationary, curvature,
    Chapter01.Section03.leastHessianEigenvalue] using hs epsilon1 epsilon2 he1 he2 he2one

/-- Theorem 3.2.7: a uniformly smooth bounded family needs at least the inverse cube of
ε successful TR2 steps before the first joint test at tolerances ε. The radius starts at ε,
as in the source construction. Both derivative oracles are counted by accepted iterations. -/
theorem theorem_3_2_7 :
    ∃ L B : ℝ, 1 ≤ L ∧ 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (delta : ℕ → ℝ),
        Chapter02.Section01.assumption_f_Bb f ∧ Section01.hessianLipschitz f L ∧
        hessianBound f B ∧ (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧ x 0 = 0 ∧ delta 0 = ε ∧
        algorithm_3_2_1 TrustRegion.sharpParameters true f x s delta ∧
        (∀ k < N, ¬Stationary f ε ε (x k)) ∧ Stationary f ε ε (x N) ∧
        (N : ℝ) + 1 ≥ 1 / ε ^ 3 ∧
        (ParameterUpdates.successCount
          (fun k => TrustRegion.sharpParameters.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
            (hessianOperator f (x k)) (x k) (s k)) N : ℝ) + 1 ≥ 1 / ε ^ 3 := by
  obtain ⟨L, B, hfamily⟩ := TrustRegionSecondOrderSharpness.exists_sharp_secondOrder_family
  refine ⟨max 1 (L : ℝ), max 1 (B : ℝ), le_max_left _ _, le_max_left _ _, ?_⟩
  intro ε hε hεone
  obtain ⟨f, N, x, s, delta, hf, hLip, hb, hH, hfx, hx, hdelta, hrun, hg, hc, hterminal,
    hcount, hN⟩ := hfamily ε hε hεone
  refine ⟨f, N, x, s, delta, ?_, Section01.hessianLipschitz.of_lipschitzWith hf hLip,
    ⟨hf, le_max_left _ _, fun y => (hH y).trans (le_max_right _ _)⟩,
    (fun y => (hb y).trans (le_max_right _ _)), hfx, hx, hdelta, hrun, ?_, ?_, ?_, ?_⟩
  · apply Chapter02.Section01.assumption_f_Bb_iff.mpr
    exact ⟨-(B : ℝ), fun y => (abs_le.mp (hb y)).1⟩
  · intro k hk hstop
    have hcurv := hstop.2
    rw [hc k hk] at hcurv
    linarith
  · exact ⟨by simpa only [hg N, norm_zero] using hε.le, by rw [hterminal]; linarith⟩
  · linarith only [hN]
  · rw [hcount]
    linarith only [hN]

/-- Theorem 3.2.2: uniformly bounded smooth objectives and Hessians admit TR2 runs with
strictly more than `⌈ε⁻²⌉` iterations and evaluations of all three oracles. The initial radius
is two. Positive iterate Hessians make the example valid with either stopping variant. -/
theorem theorem_3_2_2 :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (delta : ℕ → ℝ),
        Chapter02.Section01.assumption_f_Bb f ∧ hessianBound f B ∧
        (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧ x 0 = 0 ∧ delta 0 = 2 ∧
        (∀ second : Bool, algorithm_3_2_1 TrustRegion.sharpParameters second f x s delta) ∧
        (∀ k < N, ε < ‖gradient f (x k)‖) ∧
        Chapter02.Section01.approximateFirstOrderMinimizer f ε (x N) ∧
        (∀ ε₂ : ℝ, 0 < ε₂ →
          (∀ k < N, ¬Stationary f ε ε₂ (x k)) ∧ Stationary f ε ε₂ (x N)) ∧
        ⌈1 / ε ^ 2⌉₊ < N ∧ ⌈1 / ε ^ 2⌉₊ < N + 1 ∧
        ⌈1 / ε ^ 2⌉₊ < ParameterUpdates.successCount
          (fun k => TrustRegion.sharpParameters.eta1 ≤ TrustRegion.ratio f (gradient f (x k))
            (hessianOperator f (x k)) (x k) (s k)) N + 1 := by
  obtain ⟨B, hfamily⟩ := TrustRegionHessianSharpness.exists_sharp_firstOrder_family
  refine ⟨max 1 (B : ℝ), le_max_left _ _, ?_⟩
  intro ε he heone
  obtain ⟨f, N, x, s, delta, hf, hb, hH, hzero, hx, hdelta, hr, hpre, hlast, hc, hcount, hN⟩ :=
    hfamily ε he heone
  refine ⟨f, N, x, s, delta,
    Chapter02.Section01.assumption_f_Bb_iff.mpr
      ⟨-(B : ℝ), fun y => (abs_le.mp (hb y)).1⟩,
    ⟨hf, le_max_left _ _, fun y => (hH y).trans (le_max_right _ _)⟩,
    (fun y => (hb y).trans (le_max_right _ _)), hzero, hx, hdelta, ?_, hpre, ?_, ?_,
    hN, hN.trans (Nat.lt_succ_self N), ?_⟩
  · intro second
    cases second
    · exact ⟨hr.toIsRun, by simp⟩
    · exact hr
  · change ‖gradient f (x N)‖ ≤ ε
    rw [hlast, norm_zero]
    exact he.le
  · intro ε₂ he₂
    constructor
    · intro k hk hs
      exact (not_le.mpr (hpre k hk)) hs.1
    · exact ⟨by simpa only [hlast, norm_zero] using he.le, by rw [hc N]; linarith⟩
  · rw [hcount]
    exact hN.trans (Nat.lt_succ_self N)

end CartisGouldToint.Chapter03.Section02
