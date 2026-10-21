import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqp
import NumlibSurface.CartisGouldToint.Chapter12.Section01.TaylorCriteria
import Numlib.Optimization.HigherOrderApproximateRegularizationInner

/-!
# ARqp model-step existence and equality stopping

Positive regularization gives actual global model minimizers and admissible model steps.
Step2 equality stopping uses the actual returned inner trace: its fraction certificate
certifies a global model minimum at zero. The outer trace retains its failed test through
rejections and caching, so this stopping location is impossible at orders one and two.
-/

noncomputable section
namespace CartisGouldToint.Chapter12.Section02
open Optimization
variable {n : ℕ}

/-- The step-existence clause of Lemma12.2.9, including unit low-order radii and the
quantitative higher-order radius bound. Arbitrary-choice inner termination is separate. -/
theorem exists_arqp_modelStep (P : ARqp.Parameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f P.p L) (x : EuclideanSpace ℝ (Fin n))
    {σ : ℝ} (hσ : 0 < σ) (inherited : ℕ → ℝ) :
    ∃ trial : HigherOrderApproximateRegularization.ModelStep P f x σ inherited,
      (∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → trial.radii j = 1) ∧
      (‖trial.step‖ ≤ 1 → ∀ j, 3 ≤ j → j ≤ P.q →
        P.fraction * P.theta / (8 * (3 * derivativeFamilyConstant P.p L + σ)) *
          P.epsilon j ≤ trial.radii j) :=
  HigherOrderApproximateRegularization.exists_modelStep P hf.toHigherOrderDerivativeFamily
    (hf.one_le_constant (P.order_pos.trans P.order_le)) x hσ inherited

/-- The inner-generated correction of Lemma12.2.10 uses an outer equality stop coupled
to an actual returned inner execution on
that iteration's model. Zero decrease forces a global model minimum at zero; generic outer
nonincrease alone would not justify this conclusion. -/
theorem lemma_12_2_10_of_inner_return (P : ARqp.Parameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℕ → ℝ}
    (hf : LipschitzDerivativeFamily f P.p L) {x : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (run : algorithm_12_2_2 P f x σ δ N)
    {z : EuclideanSpace ℝ (Fin n)} {K : ℕ}
    (inner : algorithm_12_2_3 P f (run.state N).point (run.state N).sigma z K)
    (hreturn : (inner.state K).phase = .returned)
    (hstop : run.last = .stopEqual (run.state N))
    (heq : HigherOrderApproximateRegularization.model f P.p (run.state N).point
        (run.state N).sigma (inner.state K).step =
      HigherOrderApproximateRegularization.model f P.p (run.state N).point (run.state N).sigma 0) :
    3 ≤ P.q ∧ ∃ radii : ℕ → ℝ,
      Section01.IsApproxOrderMinimizer f (run.state N).point P.q P.epsilon radii := by
  have hmin := inner.isMin_zero_of_return_eq hreturn heq
  have hfail := run.failedTest_of_stopEqual hstop
  have hq : 3 ≤ P.q := by
    by_contra hq
    exact HigherOrderApproximateRegularization.not_failedTest_of_model_isMin_zero P
      hf.smooth.contDiffAt (by omega) (run.valid N le_rfl).2.1 hmin hfail
  obtain ⟨radii, hd, ha, _⟩ :=
    HigherOrderApproximateRegularization.exists_approxMinimizer_of_model_isMin_zero P
      hf.smooth.contDiffAt hmin
  exact ⟨hq, radii, {
    toIsApproxMinimizer := ha
    order_pos := P.order_pos
    epsilon_le_one := fun j hj hjq => (P.epsilon_lt_one j hj hjq).le
    radius_le_one := fun j hj hjq => (hd j hj hjq).2 }⟩

end CartisGouldToint.Chapter12.Section02
