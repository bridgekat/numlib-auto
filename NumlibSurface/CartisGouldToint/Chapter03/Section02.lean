import Numlib.Optimization.TrustRegion.Eigenpoint
import Numlib.Optimization.TrustRegion.SecondOrder.FirstOrder
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates

/-!
# Cartis–Gould–Toint, Section 3.2: negative-curvature model decrease

The eigenpoint is an actual minimizer of the quadratic Taylor polynomial on the
feasible unit-eigenvector ray. The nonnegative-curvature branch is zero, as in
(3.2.5). Lemma 3.2.3 works for every negative Hessian eigenvalue and hence for
the least eigenvalue used by TR2. The strict comparison sign in the last display
of the source proof must be non-strict; positivity follows from the negative
eigenvalue and positive radius.

The first-order complexity theorem uses the genuine TR2 trace with its second-order
test explicitly disabled. Its function, gradient and Hessian counts include initial
evaluations. The printed constants are retained when the initial gradient is nonzero;
for an initial stationary point, the successful and logarithmic constants are set to
one so the formula covers the immediate stop without undefined gradient quotients.
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

namespace CartisGouldToint

/-- A TR2 trace in the explicitly disabled-second-order-test mode. -/
abbrev tr2FirstOrderRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x s sC : ℕ → E) (Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ ε₁ : ℝ) (ε₂ : WithTop ℝ) (N : ℕ) : Prop :=
  SecondOrderTrustRegion.FirstOrderRun f x s sC Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N

/-- The successful-iteration constant printed for TR2, with immediate-stop normalization. -/
noncomputable def tr2SuccessfulConstant (G Δ η₁ η₂ γ₁ H : ℝ) : ℝ :=
  if G = 0 then 1 else 8 * H / (γ₁ * η₁ * (1 - η₂)) * max 1 (G / Δ)

/-- The logarithmic constant printed for TR2, with immediate-stop normalization. -/
noncomputable def tr2LogConstant (G Δ η₂ γ₁ γ₂ H : ℝ) : ℝ :=
  if G = 0 then 1 else
    |Real.log ((γ₁ * (1 - η₂) / (4 * H)) * min 1 (Δ / G) / Δ)| / |Real.log γ₂| + 1

/-- **Theorem 3.2.1 (first-order TR2 complexity).** Bounded actual Hessians and a
lower objective bound imply termination and the stated bounds on function, gradient
and Hessian evaluations when the second-order test is disabled (`ε₂ = ⊤`). All four
positive constants are explicit and independent of the accuracy. The source constants
are recovered for nonzero initial gradient; the initial stationary case is normalized
to include its one initial evaluation of each quantity. -/
theorem theorem_3_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s sC : ℕ → E} {Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ ε κH flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖gradient f (x i)‖) →
      tr2FirstOrderRun f x s sC Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε ⊤ N)
    (hf : ContDiff ℝ 2 f) (hHone : 1 ≤ κH)
    (hH : ∀ y, ‖SecondOrderTrustRegion.hessian f y‖ ≤ κH)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κB > 0, ∃ κC > 0,
      κS = tr2SuccessfulConstant ‖gradient f (x 0)‖ (Δ 0) η₁ η₂ γ₁ κH ∧
      κA = κS * (1 + Real.log γ₃ / |Real.log γ₂|) ∧
      κB = 1 / |Real.log γ₂| ∧
      κC = tr2LogConstant ‖gradient f (x 0)‖ (Δ 0) η₂ γ₁ γ₂ κH ∧
      ∃ K, ‖gradient f (x K)‖ ≤ ε ∧
        tr2FirstOrderRun f x s sC Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε ⊤ K ∧
        ((SecondOrderTrustRegion.functionEvaluations K : ℕ) : ℝ) ≤
          κA * (f (x 0) - flow) / ε ^ 2 + κB * |Real.log ε| + κC ∧
        ((SecondOrderTrustRegion.gradientEvaluations ρ η₁ K : ℕ) : ℝ) ≤
          κS * (f (x 0) - flow) / ε ^ 2 + 1 ∧
        ((SecondOrderTrustRegion.hessianEvaluations ρ η₁ K : ℕ) : ℝ) ≤
          κS * (f (x 0) - flow) / ε ^ 2 + 1 := by
  have h0 := hprefix 0 (by simp)
  have hLip := SecondOrderTrustRegion.gradient_lipschitz_of_hessian_bound hf
    (by linarith : 0 ≤ κH) hH
  obtain ⟨S,hS,A,hA,B,hB,C,hC,hSeq,hAeq,hBeq,hCeq,K,hstop,hK,hF,hD⟩ :=
    theorem_2_3_7 (fun N hn => (hprefix N hn).to_firstOrder hf)
      hLip hHone (fun i => hH (x i)) hlow
  have hTR2 := hprefix K (fun i hi => hK.not_terminated i hi)
  let C' := tr2LogConstant ‖gradient f (x 0)‖ (Δ 0) η₂ γ₁ γ₂ κH
  have hlog : 0 < |Real.log γ₂| := by
    have hγ₂ : 0 < γ₂ := h0.updates.gamma1_pos.trans_le h0.updates.gamma1_le_gamma2
    exact abs_pos.mpr (ne_of_lt (Real.log_neg hγ₂ h0.updates.gamma2_lt_one))
  have hC' : 0 < C' := by
    unfold C' tr2LogConstant
    split_ifs
    · norm_num
    · positivity
  have hSeq' : S = tr2SuccessfulConstant ‖gradient f (x 0)‖ (Δ 0) η₁ η₂ γ₁ κH := by
    rw [hSeq]
    unfold tr1SuccessfulConstant tr2SuccessfulConstant
    split_ifs with hG
    · rfl
    · exact FirstOrderTrustRegion.inv_decreaseConstant_self
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hG)) h0.updates.initial_pos
        h0.updates.eta1_pos
        (h0.updates.eta1_pos.trans_le h0.updates.eta1_le_eta2).le
        h0.updates.eta2_lt_one h0.updates.gamma1_pos
        (h0.updates.gamma1_le_gamma2.trans_lt h0.updates.gamma2_lt_one)
        hHone
  refine ⟨S,hS,A,hA,B,hB,C',hC',hSeq',hAeq,hBeq,rfl,K,hstop,hTR2,?_,?_⟩
  · by_cases hG : ‖gradient f (x 0)‖ = 0
    · have hK0 : K = 0 := by
        by_contra hk
        have hn := hK.not_terminated 0 (by omega)
        rw [hG] at hn
        linarith [h0.accuracy_pos]
      rw [hK0]
      have hCp : C' = 1 := by simp [C',tr2LogConstant,hG]
      rw [hCp]
      have hp : 0 ≤ A * (f (x 0) - flow) / ε ^ 2 := by
        exact div_nonneg (mul_nonneg hA.le (sub_nonneg.mpr (hlow _))) (sq_nonneg ε)
      have hq : 0 ≤ B * |Real.log ε| := mul_nonneg hB.le (abs_nonneg _)
      norm_num [SecondOrderTrustRegion.functionEvaluations]
      linarith
    · have hGpos : 0 < ‖gradient f (x 0)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hG)
      have hcpos : 0 < γ₁ * (1 - η₂) / (4 * κH) := by
        exact div_pos (mul_pos h0.updates.gamma1_pos
          (sub_pos.mpr h0.updates.eta2_lt_one)) (by positivity)
      have hlogs := FirstOrderTrustRegion.log_initial_radius_le hGpos
        h0.updates.initial_pos hcpos
      have hdom : C ≤ C' := by
        rw [hCeq]
        dsimp [C']
        rw [tr2LogConstant,ite_eq_right hG]
        have he : 2 * (κH + κH) = 4 * κH := by ring
        rw [he]
        exact add_le_add (div_le_div_of_nonneg_right hlogs hlog.le) le_rfl
      exact hF.trans (by linarith)
  · exact ⟨hD,hD⟩
end CartisGouldToint
