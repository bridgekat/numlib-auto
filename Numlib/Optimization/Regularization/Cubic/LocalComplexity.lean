import Numlib.Optimization.Regularization.Cubic.LocalConvergence
import Numlib.Optimization.EvaluationComplexity.QuadraticLocal

/-!
# Corrected finite local and global cubic iteration counts

Actual tightened cubic rules imply the quadratic recurrence. A positive natural
double-logarithm budget handles every accuracy, including the initial test.
-/

namespace CubicRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Consistent actual tightened prefixes entering the corrected region attain
the first requested derivative target within the safe double-logarithm budget.
Every intervening trial is derived to be very successful. -/
theorem exists_local_target_count {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ℓ L α ε : ℝ} {k₀ : ℕ} {xstar ustar : E}
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L) (hzero : fderiv ℝ f xstar = 0)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hα : 0 < α) (hε : 0 < ε)
    (hαbound : α ≤ localThreshold ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂))) η₂ / 2)
    (hx₀ : ‖x k₀ - xstar‖ ≤ ℓ / (4 * L)) (hg₀ : ‖fderiv ℝ f (x k₀)‖ ≤ α)
    (hprefix : ∀ N, (∀ i, k₀ ≤ i → i < N → ε < ‖fderiv ℝ f (x i)‖) →
      TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N) :
    ∃ K ≤ quadraticIterationBudget α ε,
      ‖fderiv ℝ f (x (k₀ + K))‖ ≤ ε ∧
      (∀ k < K, ε < ‖fderiv ℝ f (x (k₀ + k))‖) ∧
      TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ (k₀ + K) ∧
      ∀ k < K, η₂ ≤ ρ (k₀ + k) := by
  let cap := max (σ 0) (γ₃ * L / (1 - η₂))
  let ζ := localThreshold ℓ L θ cap η₂
  let c := localQuadraticConstant ℓ L θ cap
  let B := quadraticIterationBudget α ε
  have hbase := hprefix k₀ (by intro i hki hi; omega)
  have hcap : 0 ≤ cap := (hbase.updates.pos (Nat.zero_le k₀)).le.trans (le_max_left _ _)
  have hc : 0 < c := localQuadraticConstant_pos hℓ hL hbase.theta_pos.le hcap
  have hz : 0 < ζ := localThreshold_pos hℓ hL hbase.theta_pos hcap
    hbase.updates.eta2_lt_one
  have hαζ : α ≤ ζ := hαbound.trans (half_le_self hz.le)
  have hsmall : c * α ≤ 1 / 2 := by
    have hh := (localThreshold_bounds ℓ L θ cap η₂).1
    have hm := (le_div_iff₀ (show 0 < 2 * c by positivity)).mp hh
    have hmul := mul_le_mul_of_nonneg_left hαζ hc.le
    nlinarith only [hm, hmul]
  have hex : ∃ J ≤ B, ‖fderiv ℝ f (x (k₀ + J))‖ ≤ ε := by
    by_contra hn
    push Not at hn
    have hfail : ∀ i, k₀ ≤ i → i < k₀ + B + 1 → ε < ‖fderiv ℝ f (x i)‖ := by
      intro i hki hi
      have he : i = k₀ + (i-k₀) := by omega
      rw [he]
      exact hn (i-k₀) (by omega)
    have hrun := hprefix (k₀ + B + 1) hfail
    obtain ⟨_, hq⟩ := hrun.local_persistence hf hstar hℓ hL hzero hlip (by omega)
      hx₀ (hg₀.trans hαζ)
    have hrec : ∀ n < B, ‖fderiv ℝ f (x (k₀ + (n + 1)))‖ ≤
        c*‖fderiv ℝ f (x (k₀ + n))‖^2 := by
      intro n hn
      have hh := hq (k₀ + n) (by omega) (by omega)
      simpa only [Nat.add_assoc] using hh.2
    have hp := quadraticIterationBudget_sufficient hc.le hα hε hg₀ hsmall
      (fun n _ => norm_nonneg (fderiv ℝ f (x (k₀ + n)))) hrec
    exact (not_lt_of_ge hp) (hn B le_rfl)
  have hexall : ∃ J, ‖fderiv ℝ f (x (k₀ + J))‖ ≤ ε := by
    obtain ⟨J, _, hJ⟩ := hex
    exact ⟨J, hJ⟩
  let K := Nat.find hexall
  have hK : ‖fderiv ℝ f (x (k₀ + K))‖ ≤ ε := Nat.find_spec hexall
  have hfirst : ∀ k < K, ε < ‖fderiv ℝ f (x (k₀ + k))‖ := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hexall hk)
  have hKB : K ≤ B := by
    obtain ⟨J, hJB, hJ⟩ := hex
    exact (Nat.find_min' hexall hJ).trans hJB
  have hrun := hprefix (k₀ + K) (by
    intro i hki hi
    have he : i = k₀ + (i-k₀) := by omega
    rw [he]
    exact hfirst (i-k₀) (by omega))
  obtain ⟨_, hq⟩ := hrun.local_persistence hf hstar hℓ hL hzero hlip (by omega)
    hx₀ (hg₀.trans hαζ)
  refine ⟨K, hKB, hK, hfirst, hrun, ?_⟩
  intro k hk
  exact (hq (k₀ + k) (by omega) (by omega)).1

end CubicRegularization
