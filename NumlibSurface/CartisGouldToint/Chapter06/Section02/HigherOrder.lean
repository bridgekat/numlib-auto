import NumlibSurface.CartisGouldToint.Chapter06.Section02
import Numlib.Optimization.ConstrainedDerivativeCriticality

/-!
# Higher order ARp-CC decrease and evaluation complexity

All active orders use actual model derivatives and actual feasible trials. Small tensor errors
place objective restricted unit directions inside the model restricted unit directions.
-/

noncomputable section
open Optimization.ParameterUpdates Optimization.HigherOrderRegularization
open Optimization.ConstrainedRegularization Optimization.FeasibleCriticality
open Optimization.TaylorCriticality
namespace CartisGouldToint.Chapter06.Section02
open Section01
variable {n : ℕ} {params : Chapter02.Section04.regularizationParameters} {p N : ℕ}
  {q : Fin 3} {tau : Fin 2 → ℝ} {theta epsilon : Fin 3 → ℝ} {L S low : ℝ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : Set (EuclideanSpace ℝ (Fin n))}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}

/-- The actual next-point objective derivative gap on the model's restricted directions,
as in (6.2.14) and (6.2.16); the order-one domain is the ordinary feasible unit domain. -/
def objectiveOnModelCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (p : ℕ) (x s : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (theta epsilon : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  gapOn (fun d => -directionalDerivative f (x + s) j d)
    (modelRestrictedSteps f C p x s sigma theta epsilon j ∩ unitBall)

/-- The order-one objective-on-model measure is exactly the ordinary feasible gradient
criticality at the actual trial endpoint. -/
@[simp] theorem objectiveOnModelCriticality_first
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (p : ℕ) (x s : EuclideanSpace ℝ (Fin n)) (sigma : ℝ)
    (theta epsilon : Fin 3 → ℝ) :
    objectiveOnModelCriticality f C p x s sigma theta epsilon 0 =
      feasibleCriticality C (x + s) (fderiv ℝ f (x + s)) := by
  simp [objectiveOnModelCriticality, feasibleCriticality, feasibleSteps_inter_unitBall]

/-- The sharp Taylor plus regularizer error at active derivative order `j.val+1`. -/
theorem arpCCPrefix.directional_error
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : Convex ℝ C) {j : Fin 3} (hj : j ≤ q)
    {k : ℕ} (hk : k < N) (hS : sigma k ≤ S) {d : EuclideanSpace ℝ (Fin n)}
    (hd : ‖d‖ ≤ 1) :
    |directionalDerivative f (x k + s k) j d -
      directionalDerivative (model f p (x k) (sigma k)) (s k) j d| ≤
      (L + S) / ((p - j.val).factorial : ℝ) * ‖s k‖ ^ (p - j.val) := by
  have hjp : j.val + 1 ≤ p := by have := h.degree_ge; have := hj; omega
  have he : p - (j.val + 1) + 1 = p - j.val := by omega
  have hb := h.toFeasibleTrial.derivative_difference hf hC (j := j.val + 1)
    (by omega) (by omega) hjp hk hS
  exact (abs_diagonal_sub_le_norm _ _ hd).trans (by simpa [he] using hb)

/-- Compactness of the translated model restricted unit directions uses only closedness. -/
theorem isCompact_modelRestrictedSteps_inter_unitBall
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) (p : ℕ) (x s : EuclideanSpace ℝ (Fin n)) (sigma : ℝ)
    (theta epsilon : Fin 3 → ℝ) (j : Fin 3) :
    IsCompact (modelRestrictedSteps f C p x s sigma theta epsilon j ∩ unitBall) :=
  isCompact_restrictedFeasibleSteps_inter_unitBall _
    (hC.preimage (continuous_const.add continuous_id)) s _ _ j

/-- Zero belongs to an active model restricted unit domain at every feasible trial. -/
theorem arpCCPrefix.zero_mem_modelRestrictedSteps
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    {j : Fin 3} (hj : j ≤ q) {k : ℕ} (hk : k < N) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈
      modelRestrictedSteps f C p (x k) (s k) (sigma k) theta epsilon j ∩ unitBall := by
  simp only [Set.mem_inter_iff, mem_modelRestrictedSteps, add_zero,
    directionalDerivative_zero, abs_zero, mem_unitBall, norm_zero]
  refine ⟨⟨h.trial_feasible k hk, ?_, ?_⟩, zero_le_one⟩
  · intro hi
    exact mul_nonneg (h.theta_mem 0).1.le
      (h.epsilon_pos 0 (by have := hj; omega)).le
  · intro hi
    exact mul_nonneg (h.theta_mem 1).1.le
      (h.epsilon_pos 1 (by have := hj; omega)).le

/-- On actual model directions the objective criticality is at most the model residual
plus the sharp derivative error. -/
theorem arpCCPrefix.objectiveOnModelCriticality_le
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    {j : Fin 3} (hj : j ≤ q) {k : ℕ} (hk : k < N) (hS : sigma k ≤ S) :
    objectiveOnModelCriticality f C p (x k) (s k) (sigma k) theta epsilon j ≤
      theta j * epsilon j +
        (L + S) / ((p - j.val).factorial : ℝ) * ‖s k‖ ^ (p - j.val) := by
  have hb := gapOn_neg_diagonal_le_add_error
    (iteratedFDeriv ℝ (j.val + 1) f (x k + s k))
    (iteratedFDeriv ℝ (j.val + 1) (model f p (x k) (sigma k)) (s k))
    (isCompact_modelRestrictedSteps_inter_unitBall f hC p (x k) (s k) (sigma k)
      theta epsilon j) ⟨0, h.zero_mem_modelRestrictedSteps hj hk⟩ (Set.Subset.refl _)
    (fun _ hd => mem_unitBall.mp hd.2)
    (h.toFeasibleTrial.derivative_difference hf hconv (j := j.val + 1)
      (by omega) (by omega) (by have := h.degree_ge; have := hj; omega) hk hS)
  have he : p - (j.val + 1) + 1 = p - j.val := by
    have := h.degree_ge; have := hj; omega
  have hb' : objectiveOnModelCriticality f C p (x k) (s k) (sigma k) theta epsilon j ≤
      modelRestrictedCriticality f C p (x k) (s k) (sigma k) theta epsilon j +
        (L + S) / ((p - j.val).factorial : ℝ) * ‖s k‖ ^ (p - j.val) := by
    simpa only [directionalDerivative, objectiveOnModelCriticality,
      modelRestrictedCriticality, he] using hb
  exact hb'.trans (add_le_add (h.residuals k hk j hj) le_rfl)

/-- Small Taylor errors and the source compatibility factors imply inclusion of every
active objective restricted unit domain into the corresponding model domain. -/
theorem arpCCPrefix.restricted_unit_subset_model
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hconv : Convex ℝ C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k))
    (hS : sigma k ≤ S)
    (hsmall : ∀ i : Fin 2, i.castSucc < q →
      (L + S) / ((p - i.val).factorial : ℝ) * ‖s k‖ ^ (p - i.val) ≤
        (1 - theta i.castSucc) * epsilon i.castSucc)
    {j : Fin 3} (hj : j ≤ q) :
    restrictedFeasibleSteps f C (x (k + 1)) tau (fun i => epsilon i.castSucc) j ∩ unitBall ⊆
      modelRestrictedSteps f C p (x k) (s k) (sigma k) theta epsilon j ∩ unitBall := by
  intro d hd
  have hx : x (k + 1) = x k + s k := by rw [h.iterate k hk, ite_eq_left hs]
  refine ⟨(mem_modelRestrictedSteps _ _ _ _ _ _ _ _ _ _).mpr ⟨?_, ?_, ?_⟩, hd.2⟩
  · simpa only [hx, mem_feasibleSteps] using hd.1.1
  · intro hj1
    have he := h.directional_error hf hconv (j := 0) (by have := hj; omega) hk hS
      (mem_unitBall.mp hd.2)
    have ht := hd.1.2.1 hj1
    rw [hx] at ht
    have ht' := abs_add_le
      (directionalDerivative (model f p (x k) (sigma k)) (s k) 0 d -
        directionalDerivative f (x k + s k) 0 d)
      (directionalDerivative f (x k + s k) 0 d)
    rw [abs_sub_comm] at ht'
    have hh := hsmall 0 (by change (0 : ℕ) < q.val; have := hj; omega)
    have hc := h.compatibility 0
    have hp := (h.epsilon_pos 0 (by have := hj; omega)).le
    simp only [Fin.val_zero, Nat.sub_zero] at he hh
    change (1 + tau 0) / 2 ≤ theta 0 at hc
    change (L + S) / (p.factorial : ℝ) * ‖s k‖ ^ p ≤ (1 - theta 0) * epsilon 0 at hh
    change |directionalDerivative f (x k + s k) 0 d| ≤ tau 0 * epsilon 0 at ht
    simp only [sub_add_cancel] at ht'
    nlinarith [mul_le_mul_of_nonneg_right hc hp]
  · intro hj2
    have he := h.directional_error hf hconv (j := 1) (by have := hj; omega) hk hS
      (mem_unitBall.mp hd.2)
    have ht := hd.1.2.2 hj2
    rw [hx] at ht
    have hh := hsmall 1 (by change (1 : ℕ) < q.val; have := hj; omega)
    have hc := h.compatibility 1
    have hp := (h.epsilon_pos 1 (by have := hj; omega)).le
    simp only [Fin.val_one] at he hh
    have he' := (abs_le.mp he)
    have ht' := abs_add_le
      (directionalDerivative (model f p (x k) (sigma k)) (s k) 1 d -
        directionalDerivative f (x k + s k) 1 d)
      (directionalDerivative f (x k + s k) 1 d)
    rw [abs_sub_comm] at ht'
    change (1 + tau 1) / 2 ≤ theta 1 at hc
    change (L + S) / ((p - 1).factorial : ℝ) * ‖s k‖ ^ (p - 1) ≤
      (1 - theta 1) * epsilon 1 at hh
    change |directionalDerivative f (x k + s k) 1 d| ≤ tau 1 * epsilon 1 at ht
    simp only [sub_add_cancel] at ht'
    nlinarith [mul_le_mul_of_nonneg_right hc hp]

/-- If every active tensor error is below its tolerance margin, the accepted successor
satisfies all actual constrained objective stopping tests. -/
theorem arpCCPrefix.approximate_of_small_errors
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k))
    (hS : sigma k ≤ S)
    (hsmall : ∀ j ≤ q,
      (L + S) / ((p - j.val).factorial : ℝ) * ‖s k‖ ^ (p - j.val) ≤
        (1 - theta j) * epsilon j) :
    IsApproximateConstrainedMinimizer f C (x (k + 1)) tau epsilon q := by
  refine ⟨h.toFeasibleTrial.feasible (by omega), h.tau_mem, h.epsilon_pos, ?_⟩
  intro j hj
  have hsub := h.restricted_unit_subset_model hf hconv hk hs hS
    (fun i hi => hsmall i.castSucc hi.le) hj
  have hzero := zero_mem_restrictedFeasibleSteps_inter_unitBall f
    (h.toFeasibleTrial.feasible (by omega : k + 1 ≤ N)) tau
    (fun i => epsilon i.castSucc) j (fun i hi =>
      mul_nonneg (h.tau_mem i).1.le (h.epsilon_pos i.castSucc
        (by change i.val ≤ q.val; have := hj; omega)).le)
  have hb := gapOn_mono_set (Δ := fun d => -directionalDerivative f (x (k + 1)) j d)
    (isCompact_modelRestrictedSteps_inter_unitBall f hC p (x k) (s k) (sigma k)
      theta epsilon j)
    (continuous_directionalDerivative f (x (k + 1)) j).neg.continuousOn ⟨0, hzero⟩ hsub
  have hx : x (k + 1) = x k + s k := by rw [h.iterate k hk, ite_eq_left hs]
  have hb' : constrainedCriticality f C (x (k + 1)) tau
      (fun i => epsilon i.castSucc) j ≤
      objectiveOnModelCriticality f C p (x k) (s k) (sigma k) theta epsilon j := by
    simpa only [constrainedCriticality, objectiveOnModelCriticality, hx] using hb
  have hm := h.objectiveOnModelCriticality_le hf hC hconv hj hk hS
  have he := hsmall j hj
  exact hb'.trans (by nlinarith)

/-- A failed accepted successor stopping test forces failure of an active tensor-error
margin; no set inclusion or decrease is assumed. -/
theorem arpCCPrefix.exists_large_error_of_not_approximate
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k))
    (hS : sigma k ≤ S)
    (hnot : ¬IsApproximateConstrainedMinimizer f C (x (k + 1)) tau epsilon q) :
    ∃ j ≤ q, (1 - theta j) * epsilon j <
      (L + S) / ((p - j.val).factorial : ℝ) * ‖s k‖ ^ (p - j.val) := by
  by_contra hn
  apply hnot (h.approximate_of_small_errors hf hC hconv hk hs hS ?_)
  intro j hj
  exact le_of_not_gt (fun he => hn ⟨j, hj, he⟩)

/-- The tolerance-normalized sharp tensor error coefficient for order `j.val+1`. -/
def constrainedErrorCoefficient (p : ℕ) (j : Fin 3) (L S : ℝ)
    (theta : Fin 3 → ℝ) : ℝ :=
  (L + S) / ((p - j.val).factorial : ℝ) / (1 - theta j)

/-- The successful decrease coefficient with the actual `(p+1)!` model normalization. -/
def constrainedDecreaseConstant (params : Chapter02.Section04.regularizationParameters)
    (p : ℕ) (j : Fin 3) (L S : ℝ) (theta : Fin 3 → ℝ) : ℝ :=
  params.eta1 * params.sigmaMin / ((p + 1).factorial : ℝ) *
    (constrainedErrorCoefficient p j L S theta)⁻¹ ^
      (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ))

/-- Each successful decrease coefficient has the source factorial expression, corrected
from the transcription's `p!` prefactor to the actual model's `(p+1)!`. -/
theorem constrainedDecreaseConstant_eq_factorial
    (params : Chapter02.Section04.regularizationParameters) (p : ℕ) (j : Fin 3)
    (L S : ℝ) (theta : Fin 3 → ℝ) :
    constrainedDecreaseConstant params p j L S theta =
      params.eta1 * params.sigmaMin / ((p + 1).factorial : ℝ) *
        (((p - j.val).factorial : ℝ) * (1 - theta j) / (L + S)) ^
          (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) := by
  have he : (constrainedErrorCoefficient p j L S theta)⁻¹ =
      ((p - j.val).factorial : ℝ) * (1 - theta j) / (L + S) := by
    simp only [constrainedErrorCoefficient, inv_div, div_div]
  rw [constrainedDecreaseConstant, he]

/-- Positive error and tolerance margin give a positive decrease coefficient. -/
theorem constrainedDecreaseConstant_pos
    (params : Chapter02.Section04.regularizationParameters) (p : ℕ) (j : Fin 3)
    {L S : ℝ} {theta : Fin 3 → ℝ} (hLS : 0 < L + S) (ht : theta j < 1) :
    0 < constrainedDecreaseConstant params p j L S theta := by
  unfold constrainedDecreaseConstant constrainedErrorCoefficient
  exact mul_pos (div_pos (mul_pos params.eta1_pos params.sigmaMin_pos) (by positivity))
    (Real.rpow_pos_of_pos (inv_pos.mpr (div_pos (div_pos hLS (by positivity))
      (sub_pos.mpr ht))) _)

/-- Failure of an active error margin pays the full strict epsilon-power decrease. -/
theorem arpCCPrefix.decrease_of_large_error
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    {j : Fin 3} (hj : j ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hLS : 0 < L + S)
    (he : (1 - theta j) * epsilon j <
      (L + S) / ((p - j.val).factorial : ℝ) * ‖s k‖ ^ (p - j.val)) :
    constrainedDecreaseConstant params p j L S theta *
      epsilon j ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) <
        f (x k) - f (x (k + 1)) := by
  have ht : 0 < 1 - theta j := sub_pos.mpr (h.theta_mem j).2
  have hc : 0 < constrainedErrorCoefficient p j L S theta :=
    div_pos (div_pos hLS (by positivity)) ht
  have hb : epsilon j < constrainedErrorCoefficient p j L S theta *
      ‖s k‖ ^ (p - j.val) := by
    calc
      epsilon j < ((L + S) / ((p - j.val).factorial : ℝ) *
          ‖s k‖ ^ (p - j.val)) / (1 - theta j) :=
        (lt_div_iff₀ ht).mpr (by nlinarith only [he])
      _ = _ := by unfold constrainedErrorCoefficient; ring
  have hm : 0 < p - j.val := by have := h.degree_ge; have := hj; omega
  have hb' := rpow_measure_lt_step_power (h.epsilon_pos j hj).le hc
    (norm_nonneg (s k)) hm (Nat.succ_pos p) hb
  have hpre : 0 < params.eta1 * params.sigmaMin / ((p + 1).factorial : ℝ) :=
    div_pos (mul_pos params.eta1_pos params.sigmaMin_pos) (by positivity)
  have hb'' := mul_lt_mul_of_pos_left hb' hpre
  have hd := h.toTrialPrefix.accepted_decrease_step hk hs
  have hh := hb''.trans_le hd
  simpa only [constrainedDecreaseConstant, Nat.succ_eq_add_one, mul_assoc] using hh

/-- Lemma 6.2.2, simultaneously for every active order one through three: failure of the
next-point objective derivative gap on the actual model domain gives strict successful
decrease with the sharp factorial-normalized source constant. -/
theorem lemma_6_2_2
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : ConvexConstraintAssumptions C)
    {j : Fin 3} (hj : j ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k))
    (hfail : epsilon j <
      objectiveOnModelCriticality f C p (x k) (s k) (sigma k) theta epsilon j) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    constrainedDecreaseConstant params p j L S theta *
      epsilon j ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)) <
        f (x k) - f (x (k + 1)) := by
  dsimp only
  have hS := h.toFeasibleTrial.sigma_upper hf hC.convex (by omega : k ≤ N)
  have hLS : 0 < L + max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
    add_pos_of_nonneg_of_pos hf.nonneg
      ((h.toRegularizationPrefix.pos (by omega : 0 ≤ N)).trans_le (le_max_left _ _))
  apply h.decrease_of_large_error hj hk hs hLS
  have hb := h.objectiveOnModelCriticality_le hf hC.isClosed hC.convex hj hk hS
  nlinarith only [hb, hfail]

/-- Minimum across precisely the active orders. Inactive infinite source tolerances are
represented by omitting those entries. -/
def activeOrderMinimum (q : Fin 3) (a : Fin 3 → ℝ) : ℝ :=
  if q = 0 then a 0 else if q = 1 then min (a 0) (a 1) else min (a 0) (min (a 1) (a 2))

/-- The active minimum is bounded by every activated entry. -/
theorem activeOrderMinimum_le (q j : Fin 3) (a : Fin 3 → ℝ) (hj : j ≤ q) :
    activeOrderMinimum q a ≤ a j := by
  fin_cases q <;> fin_cases j <;> simp_all [activeOrderMinimum, min_le_iff]

/-- Positive active entries have a positive active minimum. -/
theorem activeOrderMinimum_pos (q : Fin 3) (a : Fin 3 → ℝ)
    (ha : ∀ j ≤ q, 0 < a j) : 0 < activeOrderMinimum q a := by
  fin_cases q
  · exact ha 0 le_rfl
  · exact lt_min (ha 0 (by decide)) (ha 1 le_rfl)
  · exact lt_min (ha 0 (by decide)) (lt_min (ha 1 (by decide)) (ha 2 le_rfl))

/-- The active tolerance factor appearing in the order-one, two and three source bounds. -/
def constrainedToleranceFactor (p : ℕ) (q : Fin 3) (epsilon : Fin 3 → ℝ) : ℝ :=
  activeOrderMinimum q (fun j => epsilon j ^ (((p + 1 : ℕ) : ℝ) / (p - j.val : ℕ)))

/-- At order one the tolerance factor is the source first-order epsilon power. -/
@[simp] theorem constrainedToleranceFactor_first (p : ℕ) (epsilon : Fin 3 → ℝ) :
    constrainedToleranceFactor p 0 epsilon = epsilon 0 ^ (((p + 1 : ℕ) : ℝ) / p) := rfl

/-- At order two the tolerance factor is the minimum of the first two source powers. -/
@[simp] theorem constrainedToleranceFactor_second (p : ℕ) (epsilon : Fin 3 → ℝ) :
    constrainedToleranceFactor p 1 epsilon =
      min (epsilon 0 ^ (((p + 1 : ℕ) : ℝ) / p))
        (epsilon 1 ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))) := rfl

/-- At order three the tolerance factor is precisely the source's three-power minimum. -/
@[simp] theorem constrainedToleranceFactor_third (p : ℕ) (epsilon : Fin 3 → ℝ) :
    constrainedToleranceFactor p 2 epsilon =
      min (epsilon 0 ^ (((p + 1 : ℕ) : ℝ) / p))
        (min (epsilon 1 ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
          (epsilon 2 ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))) := rfl

/-- Positive active tolerances give a positive minimum epsilon-power factor. -/
theorem constrainedToleranceFactor_pos (p : ℕ) (q : Fin 3) {epsilon : Fin 3 → ℝ}
    (he : ∀ j ≤ q, 0 < epsilon j) : 0 < constrainedToleranceFactor p q epsilon :=
  activeOrderMinimum_pos q _ (fun j hj => Real.rpow_pos_of_pos (he j hj) _)

/-- The source successful-iteration complexity constant, independent of every tolerance. -/
def constrainedComplexityConstant (params : Chapter02.Section04.regularizationParameters)
    (p : ℕ) (q : Fin 3) (L S : ℝ) (theta : Fin 3 → ℝ) : ℝ :=
  (activeOrderMinimum q (fun j => constrainedDecreaseConstant params p j L S theta))⁻¹

/-- The tolerance-independent complexity constant is positive under the source error
and model tolerance assumptions. -/
theorem constrainedComplexityConstant_pos
    (params : Chapter02.Section04.regularizationParameters) (p : ℕ) (q : Fin 3)
    {L S : ℝ} {theta : Fin 3 → ℝ} (hLS : 0 < L + S)
    (ht : ∀ j ≤ q, theta j < 1) :
    0 < constrainedComplexityConstant params p q L S theta :=
  inv_pos.mpr (activeOrderMinimum_pos q _ (fun j hj =>
    constrainedDecreaseConstant_pos params p j hLS (ht j hj)))

/-- Each successful nonterminal actual trial pays the product of the minimum decrease
coefficient and the minimum active epsilon power. -/
theorem arpCCPrefix.decrease_of_not_approximate
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    {k : ℕ} (hk : k < N) (hs : params.eta1 ≤ ratio f p (x k) (s k))
    (hS : sigma k ≤ S)
    (hnot : ¬IsApproximateConstrainedMinimizer f C (x (k + 1)) tau epsilon q) :
    activeOrderMinimum q (fun j => constrainedDecreaseConstant params p j L S theta) *
      constrainedToleranceFactor p q epsilon ≤ f (x k) - f (x (k + 1)) := by
  have hLS : 0 < L + S := add_pos_of_nonneg_of_pos hf.nonneg
    ((h.toRegularizationPrefix.pos (by omega : k ≤ N)).trans_le hS)
  obtain ⟨j, hj, he⟩ := h.exists_large_error_of_not_approximate hf hC hconv hk hs hS hnot
  have hd := (h.decrease_of_large_error hj hk hs hLS he).le
  have hK := activeOrderMinimum_pos q _ (fun i _ =>
    constrainedDecreaseConstant_pos params p i hLS (h.theta_mem i).2)
  have hT := constrainedToleranceFactor_pos p q h.epsilon_pos
  exact (mul_le_mul (activeOrderMinimum_le q j _ hj)
    (activeOrderMinimum_le q j _ hj) hT.le
    (constrainedDecreaseConstant_pos params p j hLS (h.theta_mem j).2).le).trans hd

/-- Finite actual ARp-CC prefixes satisfy the objective and cached derivative budgets
with no termination assumption. Only the failed tests at preceding iterates are needed. -/
theorem arpCCPrefix.evaluation_bounds
    (h : arpCCPrefix params p q tau theta epsilon f C x s sigma N)
    (hf : SmoothOn f C p L) (hC : IsClosed C) (hconv : Convex ℝ C)
    (hlow : ∀ y ∈ C, low ≤ f y)
    (hfirst : ∀ k < N, ¬IsApproximateConstrainedMinimizer f C (x k) tau epsilon q) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := constrainedComplexityConstant params p q L S theta *
      ((f (x 0) - low) / constrainedToleranceFactor p q epsilon)
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    (functionEvaluations N : ℝ) ≤ A * Q + A + B + 1 ∧
      (derivativeEvaluations params p f x s N : ℝ) ≤ Q + 2 := by
  dsimp only
  let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
  let K := activeOrderMinimum q (fun j => constrainedDecreaseConstant params p j L S theta)
  let T := constrainedToleranceFactor p q epsilon
  have hLS : 0 < L + S := add_pos_of_nonneg_of_pos hf.nonneg
    ((h.toRegularizationPrefix.pos (Nat.zero_le N)).trans_le (le_max_left _ _))
  have hK : 0 < K := activeOrderMinimum_pos q _ (fun j _ =>
    constrainedDecreaseConstant_pos params p j hLS (h.theta_mem j).2)
  have hT : 0 < T := constrainedToleranceFactor_pos p q h.epsilon_pos
  have hc := h.toTrialPrefix.success_count_le (mul_pos hK hT)
    (fun k hk => hlow (x k) (h.toFeasibleTrial.feasible hk))
    (fun k hk hs hn => h.decrease_of_not_approximate hf hC hconv hk hs
      (h.toFeasibleTrial.sigma_upper hf hconv (by omega)) hn) hfirst
  have ht := h.toRegularizationPrefix.total_count_le le_rfl
    (h.toFeasibleTrial.sigma_upper hf hconv le_rfl)
  have hA : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hm := mul_le_mul_of_nonneg_right hc hA
  have hid : (f (x 0) - low) / (K * T) =
      constrainedComplexityConstant params p q L S theta * ((f (x 0) - low) / T) := by
    simp only [constrainedComplexityConstant, K, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid] at hc hm
  dsimp only [S, T] at hc hm
  simp only [functionEvaluations, derivativeEvaluations, Nat.cast_add, Nat.cast_one] at hc hm ⊢
  constructor <;> linarith

/-- Available actual ARp-CC executions have a first objective stop at each order one, two
or three, requiring exactly `p≥q` and positive active tolerances.
Available legal prefixes force the first actual objective stop with the stated objective
and cached derivative costs. The epsilon-independent constant uses `(p+1)!` and the active
minimum gives precisely the source's one-, two-, or three-power denominator. -/
theorem exists_arpCC_run_with_cost
    (hf : ConstrainedSmoothnessAssumptions f C p L low)
    (hC : ConvexConstraintAssumptions C)
    (hprefix : ∀ N, (∀ k < N,
      ¬IsApproximateConstrainedMinimizer f C (x k) tau epsilon q) →
      arpCCPrefix params p q tau theta epsilon f C x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := constrainedComplexityConstant params p q L S theta *
      ((f (x 0) - low) / constrainedToleranceFactor p q epsilon)
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, algorithm_6_2_1 params p q tau theta epsilon f C x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ A * Q + A + B + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have hb : ∀ N, (∀ k < N,
      ¬IsApproximateConstrainedMinimizer f C (x k) tau epsilon q) →
      (N : ℝ) ≤ (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        (constrainedComplexityConstant params p q L
          (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))) theta *
          ((f (x 0) - low) / constrainedToleranceFactor p q epsilon)) +
        (1 + |Real.log params.gamma1| / Real.log params.gamma2) +
        Real.log (max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) / sigma 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    have hc := ((hprefix N hn).evaluation_bounds hf.toSmoothOn hC.isClosed hC.convex
      hf.lower hn).1
    exact (by simp [functionEvaluations] : (N : ℝ) ≤ (functionEvaluations N : ℝ)).trans hc
  obtain ⟨K, _, hK, hfirst⟩ := Optimization.EvaluationComplexity.exists_first_of_prefix_bound hb
  exact ⟨K, ⟨hprefix K hfirst, hK, hfirst⟩,
    (hprefix K hfirst).evaluation_bounds hf.toSmoothOn hC.isClosed hC.convex hf.lower hfirst⟩

/-- Theorem 6.2.3: for the full source range of tolerances in `(0,1]`, legal available
ARp-CC trials reach the first order-one, two, or three objective stop with the source
minimum-power evaluation budgets. The source order is `q.val+1`, and `p≥q.val+1` is part
of the actual prefix laws. -/
theorem theorem_6_2_3
    (hf : ConstrainedSmoothnessAssumptions f C p L low)
    (hC : ConvexConstraintAssumptions C)
    (hepsilon : ∀ j ≤ q, epsilon j ∈ Set.Ioc 0 1)
    (hprefix : ∀ N, (∀ k < N,
      ¬IsApproximateConstrainedMinimizer f C (x k) tau epsilon q) →
      arpCCPrefix params p q tau theta epsilon f C x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := constrainedComplexityConstant params p q L S theta *
      ((f (x 0) - low) / constrainedToleranceFactor p q epsilon)
    let A := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let B := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, algorithm_6_2_1 params p q tau theta epsilon f C x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ A * Q + A + B + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 :=
  exists_arpCC_run_with_cost hf hC (fun N hn =>
    { hprefix N hn with epsilon_pos := fun j hj => (hepsilon j hj).1 })

end CartisGouldToint.Chapter06.Section02
