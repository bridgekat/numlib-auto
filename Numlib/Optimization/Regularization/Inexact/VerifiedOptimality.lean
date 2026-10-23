import Numlib.Optimization.TrustRegion.Inexact.Decrease

/-!
# Verified optimality with a different radius for each derivative order

Regularized methods use a vector of actual optimality radii. Each computed
Taylor test has its own finite tensor-error budget. Explicit verification
certifies the true Taylor measure without an exact objective constant.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The computed all-order optimality tests and their finite error budgets,
with a separate actual radius for every derivative order. -/
structure VectorTerminationCheck {q : ℕ} (A : FormalMultilinearSeries ℝ E ℝ)
    (δ : Fin q → ℝ) (ζ : ℝ) (ε : Fin q → ℝ) (d : Fin q → E)
    (e : ℕ → ℝ) : Prop where
  radius_nonneg : ∀ a, 0 ≤ δ a
  zeta_pos : 0 < ζ
  zeta_le_one : ζ ≤ 1
  accuracy_pos : ∀ a, 0 < ε a
  approximation : ∀ a, ζ * TaylorModel.jetCriticality A (modelOrder a) (δ a) ≤
    TaylorModel.jetDecrement A (modelOrder a) (d a)
  computed_passes : ∀ a, TaylorModel.jetDecrement A (modelOrder a) (d a) ≤
    ζ / 2 * ε a * δ a ^ modelOrder a / (modelOrder a).factorial
  verified : ∀ a, tensorErrorBudget e (modelOrder a) (δ a) ≤
    ζ / 2 * ε a * δ a ^ modelOrder a / (modelOrder a).factorial

variable [ProperSpace E]

/-- Passing each actual computed test and its explicit tensor-error budget
certifies true Taylor criticality at every requested radius. -/
theorem VectorTerminationCheck.true_optimality {q : ℕ}
    {A : FormalMultilinearSeries ℝ E ℝ} {δ : Fin q → ℝ} {ζ : ℝ}
    {ε : Fin q → ℝ} {d : Fin q → E} {e : ℕ → ℝ}
    (h : VectorTerminationCheck A δ ζ ε d e) (f : E → ℝ) (x : E)
    (horacle : ∀ a, 1 ≤ a → a ≤ q → ‖A a - iteratedFDeriv ℝ a f x‖ ≤ e a)
    (a : Fin q) :
    TaylorModel.criticality f (modelOrder a) x (δ a) ≤
      ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by
  have hscale : ζ / 2 * ε a * δ a ^ modelOrder a / (modelOrder a).factorial ≤
      ε a / 2 * δ a ^ modelOrder a / (modelOrder a).factorial := by
    have hm := mul_le_mul_of_nonneg_right h.zeta_le_one
      (show 0 ≤ ε a / 2 * δ a ^ modelOrder a / (modelOrder a).factorial from
        div_nonneg (mul_nonneg (div_nonneg (h.accuracy_pos a).le (by norm_num))
          (pow_nonneg (h.radius_nonneg a) _)) (Nat.cast_nonneg _))
    convert hm using 1 <;> ring
  exact TaylorModel.criticality_le_of_verified_jet f A (modelOrder a) x (d a)
    (h.radius_nonneg a) h.zeta_pos e
    (fun b hb hba => horacle b hb (hba.trans a.isLt))
    (h.approximation a) (h.computed_passes a) ((h.verified a).trans hscale)

end InexactRegularization

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The regularized-method uniform accuracy threshold for a vector-radius floor. -/
noncomputable def verificationThreshold (q : ℕ) (ζ κ K μ : ℝ) : ℝ :=
  ζ * κ ^ q / (4 * (q.factorial : ℝ) * K) * μ ^ (q + 1)

/-- A uniform request cap and the actual radius floor imply the per-order
finite budget. This transfer lemma does not assert how a solver obtains the floor. -/
theorem tensorErrorBudget_le_of_radius_floor {q j : ℕ} (hjq : j ≤ q)
    {δ ζ κ K μ ε H : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hζ : 0 ≤ ζ)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hK : 0 < K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hμε : μ ≤ ε) (hH : 0 ≤ H) (hfloor : κ * μ ≤ δ)
    (hsmall : H ≤ verificationThreshold q ζ κ K μ) (e : ℕ → ℝ)
    (he : ∀ a, 1 ≤ a → a ≤ j → e a ≤ K * H) :
    tensorErrorBudget e j δ ≤ ζ / 2 * ε * δ ^ j / j.factorial := by
  have hbudget := tensorErrorBudget_le_two_mul hδ hδ1 (mul_nonneg hK.le hH) he
  have hbudget' : tensorErrorBudget e j δ ≤ 2 * K * H := by
    have hh := hbudget.trans (mul_le_of_le_one_right
      (show 0 ≤ 2 * (K * H) by positivity) hδ1)
    convert hh using 1; ring
  have hbound := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * K by positivity)
  have heq : 2 * K * verificationThreshold q ζ κ K μ =
      ζ / 2 * μ * ((κ * μ) ^ q / q.factorial) := by
    unfold verificationThreshold
    rw [mul_pow, pow_succ μ]
    field_simp
    ring
  rw [heq] at hbound
  have hb : 0 ≤ κ * μ := mul_nonneg hκ hμ
  have hb1 : κ * μ ≤ 1 := (mul_le_of_le_one_left hμ hκ1).trans hμ1
  have hp := pow_div_factorial_antitone hb hb1 hjq
  have hpd := div_le_div_of_nonneg_right (pow_le_pow_left₀ hb hfloor j)
    (Nat.cast_nonneg j.factorial)
  calc _ ≤ 2 * K * H := hbudget'
    _ ≤ ζ / 2 * μ * ((κ * μ) ^ q / q.factorial) := hbound
    _ ≤ ζ / 2 * ε * (δ ^ j / j.factorial) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hμε (div_nonneg hζ (by norm_num)))
        (hp.trans hpd) (div_nonneg (pow_nonneg hb _) (Nat.cast_nonneg _))
        (mul_nonneg (div_nonneg hζ (by norm_num)) (hμ.trans hμε))
    _ = _ := by ring

/-- Per-order verification follows from a common actual request cap and vector
radius floors. No derivative identities or criticality bounds are assumed. -/
theorem vectorVerification_of_uniform_cap {q : ℕ} (hq : 0 < q)
    {δ ε : Fin q → ℝ} {ζ κ K H : ℝ} (hδ : ∀ a, 0 ≤ δ a) (hδ1 : ∀ a, δ a ≤ 1)
    (hζ : 0 ≤ ζ) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hK : 0 < K)
    (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1) (hH : 0 ≤ H)
    (hfloor : ∀ a, κ * minimumAccuracy hq ε ≤ δ a)
    (hsmall : H ≤ verificationThreshold q ζ κ K (minimumAccuracy hq ε))
    (accuracy : ℕ → ℝ) (haccuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy a ≤ H) :
    ∀ a, tensorErrorBudget (fun b => K * accuracy b) (modelOrder a) (δ a) ≤
      ζ / 2 * ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by
  intro a
  exact tensorErrorBudget_le_of_radius_floor a.isLt (hδ a) (hδ1 a) hζ hκ hκ1 hK
    (minimumAccuracy_pos hq hε).le ((minimumAccuracy_le hq ε a).trans (hε1 a))
    (minimumAccuracy_le hq ε a) hH (hfloor a) hsmall _
    (fun b hb hba => mul_le_mul_of_nonneg_left
      (haccuracy b hb (hba.trans a.isLt)) hK.le)

/-- The primitive computed tests and a sufficiently small uniform request cap
produce the explicitly verified per-order termination check. The exact-oracle
case needs no small-request condition. Radius floors remain explicit inputs to
this transfer theorem until supplied by a proved solver/radius-history theorem. -/
theorem vectorTerminationCheck_of_uniform_cap {q : ℕ} (hq : 0 < q)
    (A : FormalMultilinearSeries ℝ E ℝ) (δ ε : Fin q → ℝ) (ζ κ K H : ℝ)
    (d : Fin q → E) (accuracy : ℕ → ℝ)
    (hδ : ∀ a, 0 ≤ δ a) (hδ1 : ∀ a, δ a ≤ 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hK : 0 ≤ K)
    (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1) (hH : 0 ≤ H)
    (hfloor : ∀ a, κ * minimumAccuracy hq ε ≤ δ a)
    (hsmall : K = 0 ∨ H ≤ verificationThreshold q ζ κ K (minimumAccuracy hq ε))
    (haccuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy a ≤ H)
    (happrox : ∀ a, ζ * TaylorModel.jetCriticality A (modelOrder a) (δ a) ≤
      TaylorModel.jetDecrement A (modelOrder a) (d a))
    (hpass : ∀ a, TaylorModel.jetDecrement A (modelOrder a) (d a) ≤
      ζ / 2 * ε a * δ a ^ modelOrder a / (modelOrder a).factorial) :
    VectorTerminationCheck A δ ζ ε d (fun a => K * accuracy a) := by
  refine ⟨hδ, hζ, hζ1, hε, happrox, hpass, ?_⟩
  by_cases hzero : K = 0
  · intro a
    simp only [hzero, zero_mul, tensorErrorBudget, zero_div, Finset.sum_const_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg hζ.le (by norm_num))
      (hε a).le) (pow_nonneg (hδ a) _)) (Nat.cast_nonneg _)
  · exact vectorVerification_of_uniform_cap hq hδ hδ1 hζ.le hκ hκ1
      (lt_of_le_of_ne hK (Ne.symm hzero)) hε hε1 hH hfloor
      (hsmall.resolve_left hzero) accuracy haccuracy

end InexactRegularization
