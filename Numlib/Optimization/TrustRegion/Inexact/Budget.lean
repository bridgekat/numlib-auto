import Numlib.Optimization.TrustRegion.Inexact.VerifiedOptimality

/-!
# Uniform accuracy thresholds for inexact Taylor tests

A finite factorial sum bounds the actual tensor-error budget. The operational
radius floor converts a uniform accuracy threshold into the explicit verification
test, and hence certifies both IDA true optimality and EDA stopping.
-/

namespace InexactTrustRegion
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive-order exponential sums written with zero-based finite indices. -/
theorem sum_range_succ_pow_div_factorial_le_two_mul {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (q : ℕ) :
    (∑ i ∈ Finset.range q, δ ^ (i + 1) / (i + 1).factorial) ≤ 2 * δ := by
  have heq : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by ext i; simp
  have h := Real.sum_Icc_pow_div_factorial_le_two_mul hδ hδ1 q
  rw [heq, Finset.sum_Ico_eq_sum_range] at h
  simpa only [Nat.add_sub_cancel, add_comm 1] using h

/-- A uniform cap on actual tensor errors bounds the finite Taylor error budget. -/
theorem tensorErrorBudget_le_two_mul {e : ℕ → ℝ} {q : ℕ} {δ H : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H)
    (he : ∀ a, 1 ≤ a → a ≤ q → e a ≤ H) : tensorErrorBudget e q δ ≤ 2 * H * δ := by
  calc _ ≤ ∑ i ∈ Finset.range q, H * (δ ^ (i + 1) / (i + 1).factorial) := by
        apply Finset.sum_le_sum
        intro i hi
        have hip : i + 1 ≤ q := Finset.mem_range.mp hi
        have hh := mul_le_mul_of_nonneg_right (he (i + 1) (by omega) hip)
          (div_nonneg (pow_nonneg hδ (i + 1)) (Nat.cast_nonneg (i + 1).factorial))
        simpa only [tensorErrorBudget, mul_div_assoc] using hh
    _ = H * ∑ i ∈ Finset.range q, δ ^ (i + 1) / (i + 1).factorial :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ H * (2 * δ) := mul_le_mul_of_nonneg_left
      (sum_range_succ_pow_div_factorial_le_two_mul hδ hδ1 q) hH
    _ = _ := by ring

/-- The normalized tensor-accuracy threshold, with an explicit oracle constant. -/
noncomputable def accuracyThreshold (q : ℕ) (ζ κ K μ : ℝ) : ℝ :=
  ζ ^ (q + 1) * κ ^ q / (4 * (q.factorial : ℝ) * K) * μ ^ (q + 1)

/-- The source uniform threshold, together with the proved radius floor,
implies the explicit finite error-budget verification test. -/
theorem tensorErrorBudget_le_of_accuracyThreshold {q : ℕ} {δ ζ κ K μ H : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hζ : 0 ≤ ζ) (hκ : 0 ≤ κ)
    (hK : 0 < K) (hμ : 0 ≤ μ) (hH : 0 ≤ H) (hfloor : ζ * κ * μ ≤ δ)
    (hsmall : H ≤ accuracyThreshold q ζ κ K μ) (e : ℕ → ℝ)
    (he : ∀ a, 1 ≤ a → a ≤ q → e a ≤ K * H) :
    tensorErrorBudget e q δ ≤ ζ / 2 * μ * δ ^ q / q.factorial := by
  have hfirst := tensorErrorBudget_le_two_mul hδ hδ1 (mul_nonneg hK.le hH) he
  have hδ0 : δ ≤ 1 := hδ1
  have hbudget : tensorErrorBudget e q δ ≤ 2 * (K * H) :=
    hfirst.trans (mul_le_of_le_one_right (by positivity) hδ0)
  have hfac : (0 : ℝ) < q.factorial := by positivity
  have hscale := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * K by positivity)
  have heq : 2 * K * accuracyThreshold q ζ κ K μ =
      ζ / 2 * μ * (ζ * κ * μ) ^ q / q.factorial := by
    unfold accuracyThreshold
    rw [mul_pow, mul_pow, pow_succ ζ, pow_succ μ]
    field_simp
    ring
  rw [heq] at hscale
  calc _ ≤ 2 * K * H := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hbudget
    _ ≤ ζ / 2 * μ * (ζ * κ * μ) ^ q / q.factorial := hscale
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfloor _)
        (by positivity)) hfac.le


/-- Uniformly small requested accuracies make the actual passing computed
optimality tests pass the explicit EDA error-budget check. -/
theorem terminationCheck_of_accuracyThreshold {q : ℕ}
    {A : FormalMultilinearSeries ℝ E ℝ} {δ ζ κ K μ H : ℝ}
    {ε : Fin q → ℝ} {d : Fin q → E} {accuracy : ℕ → ℝ}
    (hq : 0 < q) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hκ : 0 ≤ κ) (hK : 0 < K) (hH : 0 ≤ H) (hε : ∀ a, 0 < ε a)
    (hμ : μ = minimumAccuracy hq ε) (hfloor : ζ * κ * μ ≤ δ)
    (hsmall : H ≤ accuracyThreshold q ζ κ K μ)
    (haccuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy a ≤ H)
    (happrox : ∀ a, ζ * TaylorModel.jetCriticality A (modelOrder a) δ ≤
      TaylorModel.jetDecrement A (modelOrder a) (d a))
    (hpass : ∀ a, TaylorModel.jetDecrement A (modelOrder a) (d a) ≤
      ζ / 2 * ε a * δ ^ modelOrder a / (modelOrder a).factorial) :
    TerminationCheck A δ ζ ε d (fun a => K * accuracy a) := by
  refine ⟨hq, hδ, hδ1, hζ, hζ1, hε, happrox, hpass, ?_⟩
  rw [← hμ]
  exact tensorErrorBudget_le_of_accuracyThreshold hδ hδ1 hζ.le hκ hK
    (hμ ▸ minimumAccuracy_pos hq hε).le hH hfloor hsmall _
    (fun a ha haq => mul_le_mul_of_nonneg_left (haccuracy a ha haq) hK.le)

end InexactTrustRegion
