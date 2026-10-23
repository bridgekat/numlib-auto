import Numlib.Optimization.TrustRegion.Eigenpoint
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates

/-!
# Cartis–Gould–Toint, Section 3.2: negative-curvature model decrease

The eigenpoint is an actual minimizer of the quadratic Taylor polynomial on the
feasible unit-eigenvector ray. The nonnegative-curvature branch is zero, as in
(3.2.5). Lemma 3.2.3 works for every negative Hessian eigenvalue and hence for
the least eigenvalue used by TR2. The strict comparison sign in the last display
of the source proof must be non-strict; positivity follows from the negative
eigenvalue and positive radius.
-/

namespace CartisGouldToint

/-- The eigenstep (3.2.5): an actual ray minimizer when the specified Hessian
eigenvalue is negative, and zero in the nonnegative branch. -/
def eigenpoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x u : E) (μ Δ : ℝ) (sE : E) : Prop :=
  if μ < 0 then TaylorModel.IsEigenPoint f x u Δ sE else sE = 0

/-- The eigenstep specification has a solution at every nonnegative radius. -/
theorem eigenpoint_exists {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x u : E) (μ : ℝ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ sE, eigenpoint f x u μ Δ sE := by
  by_cases hμ : μ < 0
  · simpa only [eigenpoint, ite_eq_left hμ] using TaylorModel.exists_eigenPoint f x u hΔ
  · exact ⟨0, by simp [eigenpoint, hμ]⟩

/-- **Lemma 3.2.3.** The actual Taylor eigenpoint obtains (3.2.15), and every
trial meeting the eigenpoint-decrease condition has a strictly positive ratio
denominator. A genuine negative Hessian eigenpair is sufficient; it may in
particular be the least eigenpair specified by the algorithm. -/
theorem lemma_3_2_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x u : E) {μ Δ : ℝ} {sE s : E}
    (hΔ : 0 < Δ) (hμ : μ < 0) (hu : ‖u‖ = 1)
    (he : TaylorModel.hessianOperator f x u = μ • u)
    (hg : inner ℝ u (gradient f x) ≤ 0) (hp : eigenpoint f x u μ Δ sE)
    (hs : TaylorModel.eval f 2 x s ≤ TaylorModel.eval f 2 x sE) :
    TaylorModel.eval f 2 x sE ≤ TaylorModel.eval f 2 x 0 -
        (1 / 2 : ℝ) * |μ| * Δ ^ 2 ∧
      0 < TaylorModel.eval f 2 x 0 - TaylorModel.eval f 2 x s := by
  have hp' : TaylorModel.IsEigenPoint f x u Δ sE := by
    simpa only [eigenpoint, ite_eq_left hμ] using hp
  have hg' : inner ℝ (gradient f x) u ≤ 0 := by rwa [real_inner_comm]
  exact ⟨TaylorModel.eigenpoint_decrease f x u hΔ.le hμ hu he hg' hp',
    TaylorModel.eigenpoint_predicted_decrease_pos f x u hΔ hμ hu he hg' hp' hs⟩

/-- **Lemma 3.2.4.** The second-order small-radius threshold (3.2.16)
forces very successful acceptance, success and a nondecreasing radius. -/
theorem lemma_3_2_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x u : E) {μ L : ℝ} {sE s : E}
    {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ : ℝ} {N i : ℕ}
    (hup : EvaluationComplexity.TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N)
    (hi : i < N) (hf : ContDiff ℝ 2 f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hμ : μ < 0) (hu : ‖u‖ = 1) (he : TaylorModel.hessianOperator f x u = μ • u)
    (hg : inner ℝ u (gradient f x) ≤ 0) (hp : eigenpoint f x u μ (Δ i) sE)
    (hs : TaylorModel.eval f 2 x s ≤ TaylorModel.eval f 2 x sE) (hsnorm : ‖s‖ ≤ Δ i)
    (hsmall : Δ i < 3 * (1 - η₂) * |μ| / L)
    (hratio : ρ i = (f x - f (x + s)) /
      (TaylorModel.eval f 2 x 0 - TaylorModel.eval f 2 x s)) :
    η₂ ≤ ρ i ∧ η₁ ≤ ρ i ∧ Δ i ≤ Δ (i + 1) := by
  have hp' : TaylorModel.IsEigenPoint f x u (Δ i) sE := by
    simpa only [eigenpoint, ite_eq_left hμ] using hp
  have hg' : inner ℝ (gradient f x) u ≤ 0 := by rwa [real_inner_comm]
  have hvery := TaylorModel.eigen_trial_very_successful f x u hf hL hlip
    (hup.pos (show i ≤ N by omega)) hμ hu he hg' hp' hs hsnorm
    hup.eta2_lt_one hsmall hratio
  have hnext := hup.update i hi
  rw [ite_eq_left hvery] at hnext
  exact ⟨hvery, hup.eta1_le_eta2.trans hvery, hnext.1⟩

end CartisGouldToint
