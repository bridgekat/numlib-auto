import Numlib.Optimization.Newton.Sharpness
import Numlib.Optimization.Sharpness.SecondOrder
import Numlib.Optimization.TrustRegion.SecondOrder.Complexity
import Numlib.Optimization.TrustRegion.SecondOrder.Eigenpair
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
/-- A certified least eigenpair for the actual Hessian; the Rayleigh comparison
quantifies over every unit direction. -/
abbrev tr2LeastEigenpair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) (μ : ℝ) (u : E) : Prop :=
  SecondOrderTrustRegion.IsLeastEigenpair f x μ u

/-- The operational TR2 branch with both finite stopping tolerances. -/
abbrev tr2FiniteRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x s sC sE u : ℕ → E) (μ Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ : ℝ) (N : ℕ) : Prop :=
  SecondOrderTrustRegion.Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N

/-- **Lemma 3.2.5.** The actual finite-tolerance TR2 radius stays above
(3.2.17), with the exact printed accuracy-independent constant. A prefix of
`N` trials gives the bound also at its endpoint, even if that endpoint terminates. -/
theorem lemma_3_2_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s sC sE u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ H L : ℝ} {N : ℕ}
    (h : tr2FiniteRun f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖SecondOrderTrustRegion.hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    ∃ κΔ ∈ Set.Ioo (0 : ℝ) 1,
      κΔ = min (γ₁ * (1 - η₂) / max (4 * H) (L / 3)) (Δ 0) ∧
      ∀ i ≤ N, κΔ * min ε₁ ε₂ ≤ Δ i := by
  exact ⟨_, h.radiusConstant_mem_Ioo hH hL.le, rfl,
    fun _ hi => h.radius_lower hf hH hL hε₂ hbound hlip hi⟩


/-- **Theorem 3.2.6.** Genuine finite-tolerance TR2 terminates with both
first- and second-order stopping tests within the function, gradient and Hessian
budgets (3.2.20)–(3.2.21). All four constants are explicit and independent of
the requested tolerances. The OCR's final formula for `κF` omits the logarithm
and misnormalizes the initial radius; the corrected logarithmic allowance below
follows directly from the radius update counting lemma. The first tolerance may
be any positive real, as in the theorem, despite a stronger restriction used
unnecessarily in the source proof. -/
theorem theorem_3_2_6 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x s sC sE u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ H L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) →
      tr2FiniteRun f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖SecondOrderTrustRegion.hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κT > 0, ∃ κD > 0, ∃ κE > 0, ∃ κF > 0,
      κT = 1 / (η₁ / 2 * min (1 / (1 + H))
        ((min (γ₁ * (1 - η₂) / max (4 * H) (L / 3)) (Δ 0)) ^ 2)) ∧
      κD = κT * (1 + Real.log γ₃ / |Real.log γ₂|) ∧
      κE = 1 / |Real.log γ₂| ∧
      κF = |Real.log
        (SecondOrderTrustRegion.secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L / Δ 0)| /
          |Real.log γ₂| + 1 ∧
      ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
        tr2FiniteRun f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ K ∧
        (∀ i < K, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) ∧
        (SecondOrderTrustRegion.functionEvaluations K : ℝ) ≤
          κD * (f (x 0) - flow) / min (ε₁ ^ 2 * ε₂) (ε₂ ^ 3) +
            κE * |Real.log (min ε₁ ε₂)| + κF ∧
        (SecondOrderTrustRegion.gradientEvaluations ρ η₁ K : ℝ) ≤
          κT * (f (x 0) - flow) / min (ε₁ ^ 2 * ε₂) (ε₂ ^ 3) + 1 ∧
        (SecondOrderTrustRegion.hessianEvaluations ρ η₁ K : ℝ) ≤
          κT * (f (x 0) - flow) / min (ε₁ ^ 2 * ε₂) (ε₂ ^ 3) + 1 := by
  have h0 := hprefix 0 (by simp)
  have hc := h0.secondOrderDecreaseCoefficient_pos hH hL.le
  have hg₂ := h0.updates.gamma1_pos.trans_le h0.updates.gamma1_le_gamma2
  have hglog := Real.log_neg hg₂ h0.updates.gamma2_lt_one
  have hlp : 0 < |Real.log γ₂| := abs_pos.mpr hglog.ne
  have hA : 0 < 1 + Real.log γ₃ / |Real.log γ₂| := by
    have hg₃ := Real.log_pos h0.updates.one_lt_gamma3
    positivity
  obtain ⟨K, hg, hμ, hK, hfirst⟩ := SecondOrderTrustRegion.exists_termination
    hprefix hf hH hL hε₂ hbound hlip hlow
  let c := SecondOrderTrustRegion.secondOrderDecreaseCoefficient (Δ 0) η₁ η₂ γ₁ H L
  let A := 1 + Real.log γ₃ / |Real.log γ₂|
  let F := |Real.log
    (SecondOrderTrustRegion.secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L / Δ 0)| /
      |Real.log γ₂| + 1
  have hF : 0 < F := by dsimp [F]; positivity
  have hD :
      (((EvaluationComplexity.successfulIterations
        {i | η₁ ≤ ρ i} K).card : ℕ) : ℝ) + 1 ≤
      (1 / c) * (f (x 0) - flow) / min (ε₁ ^ 2 * ε₂) (ε₂ ^ 3) + 1 := by
    have hh := hK.successful_card_le hf hH hL hε₂ hbound hlip (hlow _)
    convert add_le_add_right hh 1 using 1 <;>
      (try dsimp [c, SecondOrderTrustRegion.secondOrderAccuracyFactor]) <;> ring
  refine ⟨1 / c, div_pos zero_lt_one hc, (1 / c) * A,
    mul_pos (div_pos zero_lt_one hc) hA, 1 / |Real.log γ₂|, div_pos zero_lt_one hlp,
    F, hF, rfl, rfl, rfl, rfl, K, hg, hμ, hK, hfirst, ?_, ?_, ?_⟩
  · have hh := hK.iterations_le hf hH hL hε₂ hbound hlip (hlow _)
    simp only [SecondOrderTrustRegion.functionEvaluations, Nat.cast_add, Nat.cast_one]
    convert add_le_add_right hh 1 using 1 <;>
      (try dsimp [c, A, F, SecondOrderTrustRegion.secondOrderAccuracyFactor]) <;> ring
  · simpa only [SecondOrderTrustRegion.gradientEvaluations,
      SecondOrderTrustRegion.derivativeEvaluations, Nat.cast_add, Nat.cast_one] using hD
  · simpa only [SecondOrderTrustRegion.hessianEvaluations,
      SecondOrderTrustRegion.derivativeEvaluations, Nat.cast_add, Nat.cast_one] using hD

/-- Every twice continuously differentiable objective on a positive-dimensional
Euclidean space has an actual least Hessian eigenpair with the TR2 descent sign. -/
theorem tr2LeastEigenpair_exists {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hf : ContDiffAt ℝ 2 f x) :
    ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin n),
      tr2LeastEigenpair f x μ u ∧ inner ℝ (gradient f x) u ≤ 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact SecondOrderTrustRegion.exists_leastEigenpair f x hf

/-- **Theorem 3.2.7.** An actual bounded-below, globally twice-smooth objective
with uniformly bounded Hessian and Lipschitz Hessian can force the full inverse-cube
TR2 iteration and evaluation lower bound. All regularity and objective-budget constants
are fixed before the accuracy. The initial radius is the requested accuracy, as in the
source construction. Every least Hessian eigenvalue is certified by the actual run.

The ceiling only gives `ε³⌈ε⁻³⌉ ≤ 2`, correcting the source proof's invalid upper
bound by one. Constant negative curvature until the final flat endpoint gives a
uniformly bounded Hermite witness and the same stated sharp complexity order. -/
theorem theorem_3_2_7 :
    ∃ L ≥ 1, ∃ B > 0,
    ∃ H ≥ 1, ∃ G > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ,
        ContDiff ℝ 2 f ∧ (∀ z, -B ≤ f z) ∧ f 0 - (-B) ≤ G ∧
        (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
        SecondOrderTrustRegion.Run f (CurvatureSharpness.grid ε)
          (fun _ => ε) (fun _ => 0) (fun _ => ε)
          (fun _ => 1) (CurvatureSharpness.curvature ε (CurvatureSharpness.horizon ε))
          (fun _ => ε) (fun _ => 1)
          (1/4) (1/2) (1/4) (1/2) 2 ε ε (CurvatureSharpness.horizon ε) ∧
        (∀ i < CurvatureSharpness.horizon ε,
          ¬(‖gradient f (CurvatureSharpness.grid ε i)‖ ≤ ε ∧
            -ε ≤ CurvatureSharpness.curvature ε (CurvatureSharpness.horizon ε) i)) ∧
        ‖gradient f (CurvatureSharpness.grid ε (CurvatureSharpness.horizon ε))‖ ≤ ε ∧
        -ε ≤ CurvatureSharpness.curvature ε
          (CurvatureSharpness.horizon ε) (CurvatureSharpness.horizon ε) ∧
        1 / ε ^ 3 ≤ (CurvatureSharpness.horizon ε : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.functionEvaluations
          (CurvatureSharpness.horizon ε) : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.gradientEvaluations
          (fun _ => 1) (1/4) (CurvatureSharpness.horizon ε) : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.hessianEvaluations
          (fun _ => 1) (1/4) (CurvatureSharpness.horizon ε) : ℝ) :=
  CurvatureSharpness.exists_slow_trustRegionRun

end CartisGouldToint

namespace CartisGouldToint
open NewtonMinimization.Sharpness in
/-- **Theorem 3.2.2.** Full TR2 can require strictly more than `ceil(ε⁻²)`
iterations and evaluations of the objective, gradient, and Hessian. Uniform
Hessian and objective budgets precede the accuracy. The same objective admits a
legal run for every finite positive second-order tolerance and for the disabled
curvature test. Radius two, the true ratio two, actual Cauchy minimizers, and
actual least Hessian eigenpairs realize all algorithm rules. -/
theorem theorem_3_2_2 {η₁ η₂ γ₁ γ₂ γ₃ : ℝ}
    (hη₁ : 0<η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂<1)
    (hγ₁ : 0<γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂<1) (hγ₃ : 1<γ₃) :
    ∃ H ≥ 1, ∃ G>0, ∀ ε : ℝ, 0<ε → ε ≤ 1 → ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ (∀ z, -G ≤ f z) ∧ f 0 - (-G) ≤ 2 * G ∧
      (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
      (∀ ε₂>0, SecondOrderTrustRegion.Run f (point ε) (fun _ => 2 * ε) (fun _ => 2 * ε)
        (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => 2)
        η₁ η₂ γ₁ γ₂ γ₃ ε ε₂ (horizon ε)) ∧
      SecondOrderTrustRegion.FirstOrderRun f (point ε) (fun _ => 2 * ε) (fun _ => 2 * ε)
        (fun _ => 2) (fun _ => 2) η₁ η₂ γ₁ γ₂ γ₃ ε ⊤ (horizon ε) ∧
      point ε 0 = 0 ∧ ‖gradient f (point ε (horizon ε))‖ ≤ ε ∧
      (∀ ε₂>0, ∀ v : ℝ, ‖v‖ = 1 → -ε₂ ≤
        iteratedFDeriv ℝ 2 f (point ε (horizon ε)) (fun _ => v)) ∧
      ⌈1 / ε ^ 2⌉₊ < horizon ε ∧
      SecondOrderTrustRegion.functionEvaluations (horizon ε) = horizon ε + 1 ∧
      SecondOrderTrustRegion.gradientEvaluations (fun _ => 2) η₁ (horizon ε) =
        horizon ε + 1 ∧
      SecondOrderTrustRegion.hessianEvaluations (fun _ => 2) η₁ (horizon ε) = horizon ε + 1 ∧
      ⌈1 / ε ^ 2⌉₊ < SecondOrderTrustRegion.functionEvaluations (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < SecondOrderTrustRegion.gradientEvaluations
        (fun _ => 2) η₁ (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < SecondOrderTrustRegion.hessianEvaluations
        (fun _ => 2) η₁ (horizon ε) :=
  NewtonMinimization.Sharpness.exists_slow_trustRegion_objective
    hη₁ hη hη₂ hγ₁ hγ hγ₂ hγ₃

end CartisGouldToint
