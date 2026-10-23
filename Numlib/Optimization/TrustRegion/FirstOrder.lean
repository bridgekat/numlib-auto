import Numlib.Optimization.TrustRegion.Cauchy
import Numlib.Optimization.LineSearch.LipschitzGradient
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# First-order trust-region traces

A trace records the actual quadratic model, a genuine Cauchy minimizer, the
objective-based acceptance ratio, the stopping test and the three radius updates.
Model decrease and sufficient success conditions are consequences of these rules.
-/

namespace FirstOrderTrustRegion

open QuadraticTrustRegion EvaluationComplexity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Operational rules of Algorithm TR1 before termination. -/
structure Run (f : E → ℝ) (g : E → E) (x s sC : ℕ → E)
    (B : ℕ → E →L[ℝ] E) (Δ ρ : ℕ → ℝ) (η₁ η₂ γ₁ γ₂ γ₃ ε : ℝ)
    (N : ℕ) : Prop where
  derivative : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y
  updates : TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N
  accuracy_pos : 0 < ε
  not_terminated : ∀ i < N, ε < ‖g (x i)‖
  cauchy : ∀ i < N, IsCauchyPoint (f (x i)) (g (x i)) (B i) (Δ i) (sC i)
  feasible_step : ∀ i < N, ‖s i‖ ≤ Δ i
  model_step : ∀ i < N,
    model (f (x i)) (g (x i)) (B i) (s i) ≤
      model (f (x i)) (g (x i)) (B i) (sC i)
  ratio : ∀ i < N, ρ i = (f (x i) - f (x i + s i)) /
    (model (f (x i)) (g (x i)) (B i) 0 - model (f (x i)) (g (x i)) (B i) (s i))
  step : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

/-- Minimum of a scalar sequence on the inclusive prefix `0,…,k`. -/
noncomputable def prefixMinimum (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' (by exact ⟨0, by simp⟩) a

/-- The prefix minimum is below each entry in that prefix. -/
theorem prefixMinimum_le (a : ℕ → ℝ) {k i : ℕ} (hi : i ≤ k) :
    prefixMinimum a k ≤ a i :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

/-- A lower bound on every prefix entry bounds its minimum. -/
theorem le_prefixMinimum {a : ℕ → ℝ} {k : ℕ} {m : ℝ}
    (hm : ∀ i ≤ k, m ≤ a i) : m ≤ prefixMinimum a k :=
  Finset.le_inf' _ _ (fun i hi => hm i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

/-- The source's accuracy-independent constant in the radius lower bound. -/
noncomputable def radiusConstant (initialGradient initialRadius η₂ γ₁ L κB : ℝ) : ℝ :=
  γ₁ * (1 - η₂) / (2 * (L + κB)) * min 1 (initialRadius / initialGradient)

/-- The source's model-decrease constant (2.3.20). -/
noncomputable def decreaseConstant (initialGradient initialRadius η₂ γ₁ L κB : ℝ) : ℝ :=
  (1 / 2 : ℝ) * min (1 / (1 + κB))
    (radiusConstant initialGradient initialRadius η₂ γ₁ L κB)

/-- The explicit model-decrease constant is positive whenever the initial
gradient is nonzero and the algorithm parameters satisfy their ranges. -/
theorem decreaseConstant_pos {initialGradient initialRadius η₂ γ₁ L κB : ℝ}
    (hg : 0 < initialGradient) (hΔ : 0 < initialRadius) (hη : η₂ < 1)
    (hγ : 0 < γ₁) (hL : 1 ≤ L) (hκ : 0 ≤ κB) :
    0 < decreaseConstant initialGradient initialRadius η₂ γ₁ L κB := by
  unfold decreaseConstant radiusConstant
  positivity

namespace Run

variable {f : E → ℝ} {g : E → E} {x s sC : ℕ → E}
  {B : ℕ → E →L[ℝ] E} {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB : ℝ} {N : ℕ}

/-- Every shorter operational prefix is again a valid trace. -/
theorem restrict (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {M : ℕ} (hM : M ≤ N) : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε M where
  derivative := h.derivative
  updates := { h.updates with update := fun i hi => h.updates.update i (lt_of_lt_of_le hi hM) }
  accuracy_pos := h.accuracy_pos
  not_terminated := fun i hi => h.not_terminated i (lt_of_lt_of_le hi hM)
  cauchy := fun i hi => h.cauchy i (lt_of_lt_of_le hi hM)
  feasible_step := fun i hi => h.feasible_step i (lt_of_lt_of_le hi hM)
  model_step := fun i hi => h.model_step i (lt_of_lt_of_le hi hM)
  ratio := fun i hi => h.ratio i (lt_of_lt_of_le hi hM)
  step := fun i hi => h.step i (lt_of_lt_of_le hi hM)

/-- The model denominator is strictly positive at each nonterminated trial. -/
theorem denominator_pos (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) :
    0 < model (f (x i)) (g (x i)) (B i) 0 -
      model (f (x i)) (g (x i)) (B i) (s i) :=
  predicted_decrease_pos (h.updates.pos (by omega))
    (norm_pos_iff.mp (h.accuracy_pos.trans (h.not_terminated i hi)))
    (h.cauchy i hi) (h.model_step i hi)

/-- Cauchy decrease transfers to every permitted trial step. -/
theorem model_decrease (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) :
    (1 / 2 : ℝ) * ‖g (x i)‖ * min (‖g (x i)‖ / (1 + ‖B i‖)) (Δ i) ≤
      model (f (x i)) (g (x i)) (B i) 0 -
        model (f (x i)) (g (x i)) (B i) (s i) := by
  have hc := cauchy_decrease (h.updates.pos (show i ≤ N by omega)).le (h.cauchy i hi)
  linarith [h.model_step i hi]

/-- The discrepancy between the objective and its actual quadratic model is
controlled by the gradient Lipschitz constant and the model operator norm. -/
theorem model_error (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) {i : ℕ} (_hi : i < N) :
    |f (x i + s i) - model (f (x i)) (g (x i)) (B i) (s i)| ≤
      (L + ‖B i‖) / 2 * ‖s i‖ ^ 2 := by
  have hderiv : ∀ y z, ‖innerSL ℝ (g y) - innerSL ℝ (g z)‖ ≤ L * ‖y - z‖ := by
    intro y z
    rw [← map_sub, innerSL_apply_norm]
    exact hL y z
  have ht := norm_sub_sub_fderiv_le_half_of_lipschitz_bound h.derivative hderiv
    (x i) (s i)
  have hb : |inner ℝ (s i) (B i (s i))| ≤ ‖B i‖ * ‖s i‖ ^ 2 := by
    calc
      _ ≤ ‖s i‖ * ‖B i (s i)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖s i‖ * (‖B i‖ * ‖s i‖) :=
        mul_le_mul_of_nonneg_left ((B i).le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  rw [Real.norm_eq_abs, innerSL_apply_apply] at ht
  have htri := abs_sub (f (x i + s i) - f (x i) - inner ℝ (g (x i)) (s i))
    ((1 / 2 : ℝ) * inner ℝ (s i) (B i (s i)))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at htri
  unfold model
  have he : f (x i + s i) - (f (x i) + inner ℝ (g (x i)) (s i) +
      (1 / 2 : ℝ) * inner ℝ (s i) (B i (s i))) =
      (f (x i + s i) - f (x i) - inner ℝ (g (x i)) (s i)) -
        (1 / 2 : ℝ) * inner ℝ (s i) (B i (s i)) := by ring
  rw [he]
  nlinarith

/-- A sufficiently small radius guarantees a very successful trial. The
threshold is the one in (2.3.15), with the source normalization `1 ≤ L`. -/
theorem very_successful (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i < N, ‖B i‖ ≤ κB) {i : ℕ} (hi : i < N)
    (hsmall : Δ i < (1 - η₂) * ‖g (x i)‖ / (2 * (L + κB))) :
    η₂ ≤ ρ i := by
  have hΔ := h.updates.pos (show i ≤ N by omega)
  have hgp := h.accuracy_pos.trans (h.not_terminated i hi)
  have hηpos := h.updates.eta1_pos.trans_le h.updates.eta1_le_eta2
  have hη := h.updates.eta2_lt_one
  have hκ : 0 ≤ κB := (norm_nonneg _).trans (hB i hi)
  have hLp : 0 < L + κB := by linarith
  have hmul := (lt_div_iff₀ (by positivity : 0 < 2 * (L + κB))).mp hsmall
  have hrad : Δ i ≤ ‖g (x i)‖ / (1 + ‖B i‖) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + ‖B i‖)).mpr
    have hb := mul_le_mul_of_nonneg_right (hB i hi) hΔ.le
    have hl := mul_le_mul_of_nonneg_right hLone hΔ.le
    nlinarith [mul_pos hηpos hgp]
  have hd := h.model_decrease hi
  rw [min_eq_right hrad] at hd
  have he := h.model_error hL hi
  have hsn : ‖s i‖ ^ 2 ≤ (Δ i) ^ 2 := by
    nlinarith [h.feasible_step i hi, norm_nonneg (s i)]
  have he' : |f (x i + s i) - model (f (x i)) (g (x i)) (B i) (s i)| ≤
      (L + κB) * (Δ i) ^ 2 := by
    calc
      _ ≤ (L + ‖B i‖) / 2 * ‖s i‖ ^ 2 := he
      _ ≤ (L + κB) / 2 * ‖s i‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right (hB i hi) (sq_nonneg ‖s i‖)]
      _ ≤ (L + κB) / 2 * (Δ i) ^ 2 :=
        mul_le_mul_of_nonneg_left hsn (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (Δ i)]
  have hscale := mul_le_mul_of_nonneg_right hmul.le hΔ.le
  have herr : f (x i + s i) - model (f (x i)) (g (x i)) (B i) (s i) ≤
      (1 - η₂) * (model (f (x i)) (g (x i)) (B i) 0 -
        model (f (x i)) (g (x i)) (B i) (s i)) := by
    have hupper := (abs_le.mp he').2
    have hdmul := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 1 - η₂)
    nlinarith
  rw [h.ratio i hi]
  apply (le_div_iff₀ (h.denominator_pos hi)).mpr
  have hm0 : model (f (x i)) (g (x i)) (B i) 0 = f (x i) := by simp [model]
  rw [hm0] at herr ⊢
  linarith

/-- A very successful trial cannot reduce the radius. -/
theorem radius_le_next_of_very_successful
    (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) (hs : η₂ ≤ ρ i) : Δ i ≤ Δ (i + 1) := by
  have hu := h.updates.update i hi
  rw [ite_eq_left hs] at hu
  exact hu.1

/-- Every lower bound on the prefix gradient norms gives an explicit lower
bound on the current radius. -/
theorem radius_lower_of_gradient_lower
    (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i < N, ‖B i‖ ≤ κB) {m : ℝ}
    (hm : ∀ i < N, m ≤ ‖g (x i)‖) {i : ℕ} (hi : i ≤ N) :
    min (Δ 0) (γ₁ * ((1 - η₂) * m / (2 * (L + κB)))) ≤ Δ i := by
  apply h.updates.min_initial_threshold_le (fun j hj hsmall => ?_) hi
  have hκ : 0 ≤ κB := (norm_nonneg _).trans (hB j hj)
  have hpos : 0 < 2 * (L + κB) := by positivity
  apply h.very_successful hL hLone hB hj
  exact hsmall.trans_le (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hm j hj)
      (by linarith [h.updates.eta2_lt_one])) hpos.le)

/-- The source coefficient times any nonnegative lower bound on the prefix
gradients is a lower bound on the current radius. -/
theorem radius_lower (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ i ≤ N, m ≤ ‖g (x i)‖) {i : ℕ} (hi : i ≤ N) :
    radiusConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * m ≤ Δ i := by
  have hκ : 0 ≤ κB := (norm_nonneg _).trans (hB 0)
  have hLp : 0 < L + κB := by linarith
  have hηp := h.updates.eta1_pos.trans_le h.updates.eta1_le_eta2
  have hη := h.updates.eta2_lt_one
  have hγp := h.updates.gamma1_pos
  have hγ : γ₁ ≤ 1 := h.updates.gamma1_le_gamma2.trans h.updates.gamma2_lt_one.le
  have hΔp := h.updates.initial_pos
  have hcap0 : 0 ≤ min 1 (Δ 0 / ‖g (x 0)‖) := by positivity
  let c := (1 - η₂) / (2 * (L + κB))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity : 0 < 2 * (L + κB))).mpr
    linarith
  have hgc0 : 0 ≤ γ₁ * c := mul_nonneg hγp.le hc0
  have hgc1 : γ₁ * c ≤ 1 := (mul_le_mul hγ hc1 hc0 (by norm_num)).trans_eq (by ring)
  have hinit : radiusConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * m ≤ Δ 0 := by
    by_cases hg0 : ‖g (x 0)‖ = 0
    · have hmz : m = 0 := by linarith [hm 0 (Nat.zero_le N)]
      simp only [hmz, mul_zero]
      exact hΔp.le
    · have hgp : 0 < ‖g (x 0)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
      have hcap := (le_div_iff₀ hgp).mp (min_le_right 1 (Δ 0 / ‖g (x 0)‖))
      have hmm := mul_le_mul_of_nonneg_left (hm 0 (Nat.zero_le N)) hcap0
      have hscaled := mul_le_mul_of_nonneg_right hgc1
        (mul_nonneg hcap0 hm0)
      calc
        _ = γ₁ * c * (min 1 (Δ 0 / ‖g (x 0)‖) * m) := by
          unfold radiusConstant c
          ring
        _ ≤ min 1 (Δ 0 / ‖g (x 0)‖) * m := by
          simpa only [one_mul] using hscaled
        _ ≤ Δ 0 := hmm.trans hcap
  have hthreshold : radiusConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * m ≤
      γ₁ * ((1 - η₂) * m / (2 * (L + κB))) := by
    have hc := mul_le_mul_of_nonneg_left (min_le_left 1 (Δ 0 / ‖g (x 0)‖))
      (mul_nonneg hgc0 hm0)
    unfold radiusConstant
    dsimp [c] at hc
    convert hc using 1 <;> ring
  exact (le_min hinit hthreshold).trans
    (h.radius_lower_of_gradient_lower hL hLone (fun j _ => hB j) (fun j hj => hm j hj.le) hi)

/-- The inclusive-prefix form of the textbook radius bound (2.3.17). -/
theorem radius_lower_prefixMinimum
    (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) :
    radiusConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB *
      prefixMinimum (fun i => ‖g (x i)‖) N ≤ Δ N :=
  h.radius_lower hL hLone hB (le_prefixMinimum (fun _ _ => norm_nonneg _))
    (fun _ hi => prefixMinimum_le _ hi) le_rfl

/-- The model-decrease estimate (2.3.19), with exactly the coefficient
(2.3.20), uses the inclusive gradient prefix ending at the trial index. -/
theorem model_decrease_prefixMinimum
    (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) {i : ℕ} (hi : i < N) :
    decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * ‖g (x i)‖ *
      prefixMinimum (fun j => ‖g (x j)‖) i ≤
      model (f (x i)) (g (x i)) (B i) 0 -
        model (f (x i)) (g (x i)) (B i) (s i) := by
  let m := prefixMinimum (fun j => ‖g (x j)‖) i
  have hm0 : 0 ≤ m := le_prefixMinimum (fun _ _ => norm_nonneg _)
  have hmi : m ≤ ‖g (x i)‖ := prefixMinimum_le _ le_rfl
  have hκ : 0 ≤ κB := (norm_nonneg _).trans (hB 0)
  have hr := (h.restrict (show i ≤ N by omega)).radius_lower_prefixMinimum hL hLone hB
  have hc := h.model_decrease hi
  let a := radiusConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB
  have hfirst : min (1 / (1 + κB)) a * m ≤ ‖g (x i)‖ / (1 + ‖B i‖) := by
    calc
      _ ≤ (1 / (1 + κB)) * m :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hm0
      _ = m / (1 + κB) := by ring
      _ ≤ ‖g (x i)‖ / (1 + κB) :=
        div_le_div_of_nonneg_right hmi (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (by linarith [hB i])
  have hsecond : min (1 / (1 + κB)) a * m ≤ Δ i :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hm0).trans hr
  have hh := mul_le_mul_of_nonneg_left (le_min hfirst hsecond)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg (g (x i))))
  unfold decreaseConstant
  change (1 / 2 : ℝ) * min (1 / (1 + κB)) a * ‖g (x i)‖ * m ≤ _
  nlinarith [hh.trans hc]

/-- Successful trials convert model reduction into objective reduction. -/
theorem successful_decrease (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    η₁ * (model (f (x i)) (g (x i)) (B i) 0 -
      model (f (x i)) (g (x i)) (B i) (s i)) ≤ f (x i) - f (x (i + 1)) := by
  have hr := (le_div_iff₀ (h.denominator_pos hi)).mp ((h.ratio i hi) ▸ hs)
  rw [h.step i hi, ite_eq_left hs]
  exact hr

/-- An unsuccessful trial leaves the objective unchanged. -/
theorem objective_eq_of_unsuccessful
    (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) (hu : ¬η₁ ≤ ρ i) : f (x (i + 1)) = f (x i) := by
  rw [h.step i hi, ite_eq_right hu]

/-- The number of successful trials is bounded by the initial objective gap
and the source's explicit, accuracy-independent decrease constant. -/
theorem successful_card_le (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) (hg0 : 0 < ‖g (x 0)‖)
    {flow : ℝ} (hlow : flow ≤ f (x N)) :
    ((EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      (f (x 0) - flow) /
        (η₁ * decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * ε ^ 2) := by
  have hκ : 0 ≤ κB := (norm_nonneg _).trans (hB 0)
  have hcpos := decreaseConstant_pos hg0 h.updates.initial_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos hLone hκ
  have hε := h.accuracy_pos
  have hη := h.updates.eta1_pos
  apply EvaluationComplexity.card_successful_le_gap_div
    (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i)) (by positivity) hlow (fun i hi hs => ?_)
    (fun i hi hu => (h.objective_eq_of_unsuccessful hi hu).le)
  have hm : ε ≤ prefixMinimum (fun j => ‖g (x j)‖) i := by
    apply le_prefixMinimum
    intro j hj
    exact (h.not_terminated j (by omega)).le
  have hgi := (h.not_terminated i hi).le
  have hprod := mul_le_mul hgi hm hε.le (norm_nonneg (g (x i)))
  have hd := h.model_decrease_prefixMinimum hL hLone hB hi
  have hd' := mul_le_mul_of_nonneg_left hprod hcpos.le
  have hd'' := mul_le_mul_of_nonneg_left (by nlinarith [hd, hd'] :
      decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * ε ^ 2 ≤
        model (f (x i)) (g (x i)) (B i) 0 -
          model (f (x i)) (g (x i)) (B i) (s i)) hη.le
  nlinarith [h.successful_decrease hi hs]

/-- A positive accuracy-dependent radius floor, using only preceding failed
stopping tests. Its fixed factor is independent of the tolerance. -/
theorem radius_floor (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) :
    min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB))) * min ε 1 ≤ Δ N := by
  let d := γ₁ * (1 - η₂) / (2 * (L + κB))
  let m := min ε 1
  have hm0 : 0 ≤ m := le_min h.accuracy_pos.le zero_le_one
  have hm1 : m ≤ 1 := min_le_right _ _
  have hfloor0 : 0 ≤ min (Δ 0) d := by
    have hκ := (norm_nonneg (B 0)).trans (hB 0)
    have hΔ := h.updates.initial_pos
    have hγ := h.updates.gamma1_pos
    have hη := h.updates.eta2_lt_one
    dsimp [d]
    positivity
  have hr := h.radius_lower_of_gradient_lower hL hLone (fun i _ => hB i)
    (m := m) (fun i hi => (min_le_left ε 1).trans (h.not_terminated i hi).le)
    (i := N) le_rfl
  have hfirst : min (Δ 0) d * m ≤ Δ 0 :=
    (mul_le_of_le_one_right hfloor0 hm1).trans (min_le_left _ _)
  have hsecond : min (Δ 0) d * m ≤ γ₁ * ((1 - η₂) * m / (2 * (L + κB))) := by
    convert mul_le_mul_of_nonneg_right (min_le_right (Δ 0) d) hm0 using 1
    dsimp [d]
    ring
  exact (le_min hfirst hsecond).trans hr

/-- The logarithmic factor contributed by the accuracy-dependent radius
floor is at most a fixed term plus `|log ε|`. -/
theorem radius_floor_log_le {r δ ε : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hε : 0 < ε) :
    |Real.log (r * min ε 1 / δ)| ≤ |Real.log (r / δ)| + |Real.log ε| := by
  have hm : 0 < min ε 1 := lt_min hε zero_lt_one
  have he : r * min ε 1 / δ = r / δ * min ε 1 := by ring
  rw [he, Real.log_mul (div_pos hr hδ).ne' hm.ne']
  have hlogm : |Real.log (min ε 1)| ≤ |Real.log ε| := by
    by_cases h : ε ≤ 1
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h), Real.log_one, abs_zero]
      exact abs_nonneg _
  exact (abs_add_le _ _).trans (add_le_add le_rfl hlogm)

/-- Every nonterminated prefix satisfies the total TR1 iteration bound,
with constants fixed independently of the requested accuracy. -/
theorem iterations_le (h : Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) (hg0 : 0 < ‖g (x 0)‖)
    {flow : ℝ} (hlow : flow ≤ f (x N)) :
    (N : ℝ) ≤ (f (x 0) - flow) /
        (η₁ * decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * ε ^ 2) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log (min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB))) / Δ 0)| +
        |Real.log ε|) / |Real.log γ₂| := by
  let r := min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB)))
  have hκ := (norm_nonneg (B 0)).trans (hB 0)
  have hε := h.accuracy_pos
  have hδ := h.updates.initial_pos
  have hη := h.updates.eta2_lt_one
  have hγ := h.updates.gamma1_pos
  have hr : 0 < r := by dsimp [r]; positivity
  have ht := EvaluationComplexity.iteration_bound_of_parameter_lower
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.updates.pos hi)
    (by linarith [h.updates.one_lt_gamma3])
    (h.updates.gamma1_pos.trans_le h.updates.gamma1_le_gamma2)
    h.updates.gamma2_lt_one (h.radius_floor hL hLone hB)
    (mul_pos hr (lt_min hε zero_lt_one))
    (fun _ hi hs => h.updates.successful_le hi hs)
    (fun _ hi hu => h.updates.unsuccessful_le hi hu)
  have hA : 0 ≤ 1 + Real.log γ₃ / |Real.log γ₂| := by
    have hg3 := Real.log_pos h.updates.one_lt_gamma3
    positivity
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hL hLone hB hg0 hlow) hA)
    (div_le_div_of_nonneg_right (radius_floor_log_le hr hδ hε) (abs_nonneg _)))

end Run
/-- A consistent TR1 execution must terminate. The proof contradicts the
finite prefix bound; termination and iteration counts are not trace hypotheses. -/
theorem exists_termination {f : E → ℝ} {g : E → E} {x s sC : ℕ → E}
    {B : ℕ → E →L[ℝ] E} {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) →
      Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖g (x K)‖ ≤ ε ∧ Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε K := by
  have hex : ∃ K, ‖g (x K)‖ ≤ ε := by
    by_contra hnone
    push Not at hnone
    have h0 := hprefix 0 (by simp)
    have hg0 := h0.accuracy_pos.trans (hnone 0)
    let bound := (f (x 0) - flow) /
        (η₁ * decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB * ε ^ 2) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log (min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB))) / Δ 0)| +
        |Real.log ε|) / |Real.log γ₂|
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hnone i)).iterations_le hL hLone hB hg0 (hlow _)
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_⟩
  intro i hi
  exact lt_of_not_ge (Nat.find_min hex hi)

end FirstOrderTrustRegion
