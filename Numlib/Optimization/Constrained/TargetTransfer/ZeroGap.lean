import Numlib.Optimization.Constrained.TargetTransfer
import Numlib.Optimization.LeastNorm.Run


/-!
# Zero target gaps

Zero target gaps are classified without dividing by zero: retain the actual squared objective-
increment Taylor error for higher-order constraint-violation certificates.
-/

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- The actual squared objective increment S_x(z)=(f(z)-f(x))^2/2. -/
noncomputable def objectiveIncrementMerit (f : E → ℝ) (x z : E) : ℝ :=
  (f z - f x) ^ 2 / 2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F] in
/-- At zero target gap the actual merit equals the constraint violation plus S_x. -/
theorem targetMerit_zero_gap_decomposition (f : E → ℝ) (c : E → F) (x : E) :
    targetMerit f c (f x) = LeastNorm.merit c + objectiveIncrementMerit f x := by
  rfl

/-- Finite pointwise objective smoothness implies finite smoothness of S_x. -/
theorem contDiffAt_objectiveIncrementMerit {f : E → ℝ} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) : ContDiffAt ℝ p (objectiveIncrementMerit f x) x := by
  exact ((hf.sub contDiffAt_const).pow 2).div_const 2

/-- The actual finite merit decrement at zero target gap splits into violation and S_x
decrements. -/
theorem decrement_targetMerit_zero_gap {f : E → ℝ} {c : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x) (d : E) :
    TaylorModel.decrement (targetMerit f c (f x)) p x d =
      TaylorModel.decrement (LeastNorm.merit c) p x d +
        TaylorModel.decrement (objectiveIncrementMerit f x) p x d := by
  rw [targetMerit_zero_gap_decomposition]
  exact TaylorModel.decrement_add_of_contDiffAt
    (by exact (hc.norm_sq (𝕜 := ℝ)).div_const 2)
    (contDiffAt_objectiveIncrementMerit hf) d

/-- The actual first derivative of S_x vanishes at its base point. -/
theorem hasFDerivAt_objectiveIncrementMerit {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (objectiveIncrementMerit f x) (0 : E →L[ℝ] ℝ) x := by
  have hh := ((hf.hasFDerivAt.sub_const (f x)).pow 2).const_smul (1 / 2 : ℝ)
  convert hh using 1
  · funext z
    simp only [objectiveIncrementMerit, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

variable [ProperSpace E]
/-- Transfer normalized actual zero-gap merit criticality to constraint-violation criticality
with the actual S_x Taylor error retained. -/
theorem violation_bound_of_zero_gap_merit_certificate
    {f : E → ℝ} {c : E → F} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    {δ ε : ℝ} {X : Set E} (hX : IsClosed X) (hx : x ∈ X) (hδ : 0 ≤ δ)
    (hcrit : TaylorModel.constrainedCriticality (targetMerit f c (f x)) p X x δ ≤
      ε * ‖c x‖ * δ ^ p / p.factorial) :
    TaylorModel.constrainedCriticality (LeastNorm.merit c) p X x δ ≤
      ε * ‖c x‖ * δ ^ p / p.factorial +
        targetTaylorBound (objectiveIncrementMerit f x) p x δ := by
  obtain ⟨d, hfeas, hd, he⟩ := TaylorModel.exists_decrement_eq_constrainedCriticality
    (LeastNorm.merit c) p hX hx hδ
  have hmerit := (TaylorModel.decrement_le_constrainedCriticality
    (targetMerit f c (f x)) p hX hfeas hd).trans hcrit
  have herror := abs_decrement_le_targetTaylorBound (objectiveIncrementMerit f x) p x hd
  rw [decrement_targetMerit_zero_gap hf hc d] at hmerit
  rw [←he]
  linarith [(abs_le.mp herror).1]

/-- The actual first-order zero-gap merit certificate transfers without error to constraint-
violation criticality. -/
theorem violation_first_order_of_zero_gap_merit_certificate
    {f : E → ℝ} {c : E → F} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hc : ContDiffAt ℝ 1 c x)
    {δ ε : ℝ} {X : Set E} (hX : IsClosed X) (hx : x ∈ X) (hδ : 0 ≤ δ)
    (hcrit : TaylorModel.constrainedCriticality (targetMerit f c (f x)) 1 X x δ ≤
      ε * ‖c x‖ * δ) :
    TaylorModel.constrainedCriticality (LeastNorm.merit c) 1 X x δ ≤
      ε * ‖c x‖ * δ := by
  have hb := violation_bound_of_zero_gap_merit_certificate hf hc hX hx hδ
    (by simpa using hcrit)
  have hd := (hasFDerivAt_objectiveIncrementMerit
    (hf.differentiableAt (by norm_num))).fderiv
  simpa [targetTaylorBound, norm_iteratedFDeriv_one, hd] using hb

end Constrained
