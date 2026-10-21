import Numlib.Optimization.InexactRegularizationAccuracy
import Numlib.Optimization.InexactTaylorModelBounds

/-!
# Radius floors for supplied regularization models

The polynomial coefficients and the radial highest term share one factorial tail. Bounding
that joint tail avoids adding two independent worst-case constants, and gives the radius
floor for actual inner executions and the inherited radii of implicit-accuracy executions.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.InexactTaylorModels
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual supplied tensors give the small-radius decrease property with the common
constant `3 * max L σ`, including all positive criticality orders. -/
theorem smallRadiusDecrease_regularizedPolynomial
    (P : HigherOrderApproximateRegularization.Parameters) (c : ℝ)
    (A : InexactRegularization.Coefficients E) {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ L) :
    HigherOrderApproximateRegularization.SmallRadiusDecrease P
      (regularizedPolynomial c A P.p σ) (3 * max L σ) := by
  intro s hs j hj hjq δ hδ hδ1 hsmall d hd hdec
  apply (diagonalLipschitz_regularizedPolynomial c A P.p hσ).half_decrease_of_small_radius
    (P.order_pos.trans P.order_le) (hjq.trans P.order_le)
    (by positivity) (by have := le_max_right L σ; have := le_max_left L σ; linarith)
    ⟨hδ.le, hδ1⟩ s d hd ?_ hsmall hdec
  intro i hi
  exact norm_iteratedFDeriv_regularizedPolynomial_le_three_max
    (by have := Finset.mem_Icc.mp hi; omega) (Finset.mem_Icc.mp hi).2 c A hL hσ
    (fun k hk => hA k (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hi).1; have := (Finset.mem_Icc.mp hk).1; omega,
        (Finset.mem_Icc.mp hk).2⟩)) s hs

end Optimization.InexactTaylorModels

namespace Optimization.InexactRegularization
open InexactTaylorModels

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The detailed inner procedure can return an actual minimizer while retaining any
prescribed comparison displacement. The initialization fraction one is an allowed choice. -/
theorem exists_innerResult (P : Parameters) (c : ℝ) (A : Coefficients E)
    {σ L : ℝ} (hσ : 0 < σ) (hL : 1 ≤ L)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ L) (δ : ℕ → ℝ) (d : E) :
    Nonempty (InnerResult P c A σ δ d) := by
  let m := regularizedPolynomial c A P.p σ
  obtain ⟨z, hz⟩ := exists_regularizedPolynomial_minimizer c A P.p hσ
  let a : HigherOrderApproximateRegularization.InnerState E :=
    ⟨1, fun _ => 1, 0, .minimize⟩
  have ha : HigherOrderApproximateRegularization.InnerInitial a :=
    ⟨by norm_num [a], by norm_num [a], rfl, rfl⟩
  obtain ⟨N, run, hzero, hreturn⟩ :=
    HigherOrderApproximateRegularization.exists_inner_return_execution P.toParameters
      (M := 3 * max L σ) (by have := le_max_left L σ; linarith)
      ((contDiff_regularizedPolynomial c A P.p σ).of_le (by exact_mod_cast P.order_le))
      (isCompact_regularizedPolynomial_sublevel c A P.p hσ (m 0)) hz
      (smallRadiusDecrease_regularizedPolynomial P.toParameters c A (by linarith) hσ.le hA) ha
  have hμ : ∀ k, k ≤ N → (run.state k).mu = 1 := by
    intro k hk
    induction k with
    | zero => rw [hzero]
    | succ k ih =>
      have hi := ih (by omega)
      have hb := (run.transition k (by omega)).mu_bounds (by rw [hi]; norm_num)
        (by rw [hi])
      linarith [hb.2.1, hb.2.2]
  refine ⟨⟨z, N, run, hreturn, ?_⟩⟩
  have hf := run.fraction_of_ne_minimize le_rfl (by rw [hreturn]; decide)
  rw [hμ N le_rfl, one_mul] at hf
  exact (by linarith : m (run.state N).step ≤ m z).trans (hz d)

/-- A short output of the actual inner procedure retains unit low-order radii and the
joint polynomial/radial higher-order floor. -/
theorem InnerResult.radii_bounds {P : Parameters} {c : ℝ} {A : Coefficients E}
    {σ L : ℝ} {δ : ℕ → ℝ} {d : E} (s : InnerResult P c A σ δ d)
    (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ L)
    (hs : ‖s.step‖ < 1) :
    (∀ j, j ≤ 2 → s.radii j = 1) ∧
      ∀ j, 3 ≤ j → j ≤ P.q →
        P.fraction * P.theta / (24 * max L σ) * P.epsilon j ≤ s.radii j := by
  have hb := s.execution.bounds (M := 3 * max L σ)
    (by have := le_max_left L σ; linarith)
    (smallRadiusDecrease_regularizedPolynomial P.toParameters c A
      (by linarith) hσ hA) (k := s.length) le_rfl
  have he : s.radii = (s.execution.state s.length).radii := by
    exact ite_eq_right (not_le_of_gt hs)
  rw [he]
  refine ⟨hb.radii_low, fun j hj hjq => ?_⟩
  convert hb.radii_floor j hj hjq using 1
  unfold HigherOrderApproximateRegularization.radiusFloor
    HigherOrderApproximateRegularization.accuracyTarget
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A uniformly accurate request passes every short-step coefficient test once its
common lower bound on the step has been established. Zero lower bounds are included. -/
theorem stepAccurate_of_uniform_request {P : Parameters} {h : ℕ → ℝ} {s : E}
    {a : ℝ} (ha : 0 ≤ a) (hlower : a ≤ ‖s‖)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h i ≤ P.kappaStep * a ^ P.p) :
    StepAccurate P P.p h s := by
  by_cases hs : 1 ≤ ‖s‖
  · exact Or.inl hs
  · apply Or.inr
    intro i hi
    have hpi : P.p - i + 1 ≤ P.p := by have := Finset.mem_Icc.mp hi; omega
    exact (hh i hi).trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ ha hlower P.p).trans
        (pow_le_pow_of_le_one (norm_nonneg s) (le_of_not_ge hs) hpi)) P.kappaStep_pos.le)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A coefficient bound controls the model decrease linearly in a step inside the unit
ball. The nonnegative regularizer can only reduce that decrease. -/
theorem regularized_decrease_le_norm [NormedSpace ℝ E] (c : ℝ) (A : Coefficients E) (p : ℕ)
    {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hA : ∀ i ∈ Finset.Icc 1 p, ‖A i‖ ≤ L) (s : E) (hs : ‖s‖ ≤ 1) :
    c - regularizedPolynomial c A p σ s ≤ 2 * L * ‖s‖ := by
  have hd : decrement A p s ≤ 2 * L * ‖s‖ := by
    have he := decrement_error_le A (fun _ => 0) (fun _ => L) p s
      (by simpa using hA)
    have hz : decrement (fun _ => 0) p s = 0 := by
      simp [decrement]
    rw [hz, sub_zero] at he
    apply (le_abs_self _).trans (he.trans ?_)
    calc
      _ ≤ ∑ i ∈ Finset.Icc 1 p, (L * ‖s‖) * (1 / (i ! : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hp : ‖s‖ ^ i ≤ ‖s‖ := by
          simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg s) hs
            (Finset.mem_Icc.mp hi).1
        simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hL)
            (by positivity : 0 ≤ (i ! : ℝ)⁻¹)
      _ = (L * ‖s‖) * ∑ i ∈ Finset.Icc 1 p, (1 / (i ! : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left (sum_inv_factorial_le_two p)
          (mul_nonneg hL (norm_nonneg s))
        nlinarith only [hb]
  have he := decrement_eq c A p s
  rw [polynomial_zero] at he
  have hn : 0 ≤ σ * ‖s‖ ^ (p + 1) / ((p + 1)! : ℝ) := by positivity
  unfold regularizedPolynomial
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A retained Step 1 witness gives an actual lower bound on the returned short step.
The tolerance and radius floor are independent inputs; no decrease-rate conclusion is assumed. -/
theorem InnerResult.norm_lower [NormedSpace ℝ E] {P : Parameters} {c : ℝ} {A : Coefficients E}
    {σ L : ℝ} {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hq : I.order ≤ P.q)
    (s : InnerResult P c A σ I.radii (I.direction hq))
    (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ L)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hεj : ε ≤ P.epsilon I.order) (hlower : κ * ε ≤ I.radii I.order)
    (hs : ‖s.step‖ ≤ 1) :
    P.fraction * κ ^ P.q * ε ^ (P.q + 1) /
      (12 * (P.q ! : ℝ) * max L σ) ≤ ‖s.step‖ := by
  have hv := I.valid_radii hδ I.order I.order_pos hq
  have hεo := P.epsilon_pos I.order I.order_pos hq
  have hvf := P.fraction_pos
  have hpow := pow_nonneg hv.1.le I.order
  have hscale : κ ^ P.q * ε ^ (P.q + 1) ≤
      P.epsilon I.order * I.radii I.order ^ I.order := by
    calc
      _ = ε * (κ * ε) ^ P.q := by rw [mul_pow, pow_succ]; ring
      _ ≤ ε * I.radii I.order ^ P.q := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hκ hε) hlower _) hε
      _ ≤ ε * I.radii I.order ^ I.order := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hv.1.le hv.2 hq) hε
      _ ≤ _ := mul_le_mul_of_nonneg_right hεj hpow
  have hfac : (I.order ! : ℝ) ≤ (P.q ! : ℝ) := by exact_mod_cast Nat.factorial_le hq
  have hpos : 0 < max L σ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hdec : P.fraction * P.epsilon I.order * I.radii I.order ^ I.order /
      (4 * (I.order ! : ℝ)) ≤ c - regularizedPolynomial c A P.p σ s.step := by
    have hr := I.retained hq
    have he : I.radii I.order = halvedRadius (δ I.order) (I.halvings I.order) := by
      simp [Inspection.radii]
    rw [← he] at hr
    change _ ≤ c - regularizedPolynomial c A P.p σ (I.direction hq) at hr
    exact hr.trans (sub_le_sub_left s.retained c)
  have hb := hdec.trans (regularized_decrease_le_norm c A P.p (by linarith) hσ hA s.step hs)
  have hh : P.fraction * κ ^ P.q * ε ^ (P.q + 1) /
      (4 * (P.q ! : ℝ)) ≤ 2 * L * ‖s.step‖ := by
    apply le_trans _ hb
    calc
      _ ≤ P.fraction * (P.epsilon I.order * I.radii I.order ^ I.order) /
          (4 * (P.q ! : ℝ)) := div_le_div_of_nonneg_right
        (by nlinarith [P.fraction_pos]) (by positivity)
      _ ≤ _ := by
        rw [mul_assoc]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have hf0 : 0 < (P.q ! : ℝ) := by positivity
  have hineq := (div_le_iff₀ (show 0 < 4 * (P.q ! : ℝ) by positivity)).mp hh
  apply (div_le_iff₀ (by positivity : 0 < 12 * (P.q ! : ℝ) * max L σ)).mpr
  have hm : 2 * L ≤ 3 * max L σ := by have := le_max_left L σ; linarith
  have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg s.step)
  nlinarith [mul_le_mul_of_nonneg_left hm' hf0.le]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A single inspection retains at least the minimum of its incoming radius and the
fixed common radius floor, at every active order including unvisited ones. -/
theorem Inspection.radii_lower [NormedSpace ℝ E] {P : Parameters} {c : ℝ} {A : Coefficients E}
    {σ L B : ℝ} {δ : ℕ → ℝ} (I : Inspection P c A σ δ)
    (hL : 1 ≤ L) (hσ : σ ≤ B)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ L)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    min (P.fraction * P.theta / (24 * max L B) * P.epsilon j) (δ j) ≤ I.radii j := by
  by_cases hjo : j ≤ I.order
  · have hb := (I.search_bounds (by linarith) hδ hA hj hjq hjo).2.1
    apply le_trans _ hb
    apply min_le_min_right
    have hM : 0 < max L σ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hB : 0 < max L B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hm : max L σ ≤ max L B := max_le_max_left L hσ
    have hε := (P.epsilon_pos j hj hjq).le
    have ht := P.theta_lt_one.le
    have hv := P.fraction_pos.le
    have hs : P.fraction * P.theta / (24 * max L B) * P.epsilon j ≤
        P.fraction * P.epsilon j / (16 * max L σ) := by
      apply (le_div_iff₀ (by positivity : 0 < 16 * max L σ)).mpr
      have hcoeff : P.fraction * P.theta / (24 * max L B) ≤
          P.fraction / (16 * max L σ) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 24 * max L B)
          (by positivity : 0 < 16 * max L σ)).mpr
        have ht' : P.fraction * P.theta ≤ P.fraction :=
          mul_le_of_le_one_right hv ht
        nlinarith [mul_le_mul_of_nonneg_left hm hv]
      have hh := mul_le_mul_of_nonneg_right hcoeff hε
      have hd : (16 * max L σ) ≠ 0 := by positivity
      calc
        _ ≤ (P.fraction / (16 * max L σ) * P.epsilon j) * (16 * max L σ) :=
          mul_le_mul_of_nonneg_right hh (by positivity)
        _ = _ := by field_simp
    exact hs
  · simp only [Inspection.radii, ite_eq_right hjo]
    exact min_le_right _ _

/-- A legal transition preserves a common radius floor, using the actual inspected and
returned radii and restoring the pre-inspection radii on accuracy-only branches. -/
theorem Transition.radii_lower {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) {L B : ℝ}
    (hL : 1 ≤ L) (hσ0 : 0 ≤ a.sigma) (hσ : a.sigma ≤ B)
    (hv : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖oracle a.point a.request i‖ ≤ L)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q)
    (hprev : P.fraction * P.theta / (24 * max L B) * P.epsilon j ≤ a.radii j) :
    P.fraction * P.theta / (24 * max L B) * P.epsilon j ≤ b.radii j := by
  have hB : 0 < max L B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hcoef : P.fraction * P.theta / (24 * max L B) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 24 * max L B)).mpr
    have hvθ : P.fraction * P.theta ≤ 1 :=
      (mul_le_mul_of_nonneg_right P.fraction_le_one P.theta_pos.le).trans
        (by simpa using P.theta_lt_one.le)
    have := le_max_left L B
    linarith
  have htarget : P.fraction * P.theta / (24 * max L B) * P.epsilon j ≤ 1 :=
    (mul_le_of_le_one_left (P.epsilon_pos j hj hjq).le hcoef).trans
      (P.epsilon_lt_one j hj hjq).le
  cases t with
  | refineInspection => exact hprev
  | refineStep => exact hprev
  | trial I hq s hacc next hu =>
    have hi := le_trans (le_min le_rfl hprev)
      (I.radii_lower hL hσ hv hA hj hjq)
    split_ifs
    · change _ ≤ s.radii j
      by_cases hs : 1 ≤ ‖s.step‖
      · simpa only [InnerResult.radii, ite_eq_left hs] using hi
      · have hb := s.radii_bounds hL hσ0 hA (lt_of_not_ge hs)
        by_cases hj2 : j ≤ 2
        · rw [hb.1 j hj2]
          exact htarget
        · have hr := hb.2 j (by omega) hjq
          apply le_trans _ hr
          apply mul_le_mul_of_nonneg_right _ (P.epsilon_pos j hj hjq).le
          apply div_le_div_of_nonneg_left (mul_nonneg P.fraction_pos.le P.theta_pos.le)
            (by positivity) (by gcongr)
    · exact hi

/-- A fixed upper bound for all encountered regularization parameters gives a historical
radius floor through both accuracy-refinement branches, accepted steps and rejected trials.
The bound is independent of the checked derivative degree. -/
theorem Execution.radii_lower {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {L B : ℝ} (hL : 1 ≤ L)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ B)
    (hA : ∀ k < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i‖ ≤ L)
    {k : ℕ} (hk : k ≤ N) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    P.fraction * P.theta / (24 * max L B) * P.epsilon j ≤ (r.state k).radii j := by
  induction k with
  | zero =>
    apply le_trans _ (r.initial_tolerance j hj hjq)
    apply mul_le_of_le_one_left (P.epsilon_pos j hj hjq).le
    apply (div_le_one (by have := le_max_left L B; positivity : 0 < 24 * max L B)).mpr
    have hvθ : P.fraction * P.theta ≤ 1 :=
      (mul_le_mul_of_nonneg_right P.fraction_le_one P.theta_pos.le).trans
        (by simpa using P.theta_lt_one.le)
    have := le_max_left L B
    linarith
  | succ k ih =>
    exact (r.transition k (by omega)).radii_lower hL
      (P.sigmaMin_pos.le.trans (r.sigma_floor (by omega))) (hσ k (by omega))
      (r.valid_radii (by omega)) (hA k (by omega)) hj hjq (ih (by omega))

/-- The actual incoming history and current halving searches give the same common floor
at the post-inspection radii, including an all-pass inspection that triggers refinement. -/
theorem Execution.inspection_radii_lower {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {L B : ℝ} (hL : 1 ≤ L)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ B)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i‖ ≤ L)
    (I : Inspection P (f (r.state N).point)
      (oracle (r.state N).point (r.state N).request) (r.state N).sigma (r.state N).radii)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    P.fraction * P.theta / (24 * max L B) * P.epsilon j ≤ I.radii j := by
  exact le_trans (le_min le_rfl
    (r.radii_lower hL hσ (fun k hk => hA k hk.le) le_rfl hj hjq))
    (I.radii_lower hL (hσ N le_rfl) (r.valid_radii le_rfl) (hA N le_rfl) hj hjq)

end Optimization.InexactRegularization

namespace Optimization.InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A prefix reuses every recorded state and decision and restricts only the transition range. -/
noncomputable def Execution.prefix {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N k : ℕ}
    (r : Execution P checked f oracle N) (hk : k ≤ N) : Execution P checked f oracle k where
  state := r.state
  trial := r.trial
  accepted := r.accepted
  initial_fresh := r.initial_fresh
  initial_sigma := r.initial_sigma
  initial_radii := r.initial_radii
  initial_tolerance := r.initial_tolerance
  initial_request := r.initial_request
  initial_request_le := r.initial_request_le
  transition := fun l hl => r.transition l (hl.trans_le hk)

/-- Prefixing retains the exact original state function. -/
@[simp] theorem Execution.prefix_state {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N k : ℕ}
    (r : Execution P checked f oracle N) (hk : k ≤ N) : (r.prefix hk).state = r.state := rfl

/-- Prefixing retains the exact original trial decisions. -/
@[simp] theorem Execution.prefix_trial {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N k : ℕ}
    (r : Execution P checked f oracle N) (hk : k ≤ N) : (r.prefix hk).trial = r.trial := rfl

/-- Prefixing retains the exact original acceptance decisions. -/
@[simp] theorem Execution.prefix_accepted {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N k : ℕ}
    (r : Execution P checked f oracle N) (hk : k ≤ N) : (r.prefix hk).accepted = r.accepted := rfl

/-- The running maximum is computed from actual regularization parameters, including the
current endpoint. It requires no analytic all-iteration upper-bound theorem. -/
noncomputable def Execution.runningSigma {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sup' ⟨0, by simp⟩ (fun l => (r.state l).sigma)

/-- Every parameter already encountered is below the actual running maximum. -/
theorem Execution.sigma_le_running {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {k l : ℕ} (hl : l ≤ k) :
    (r.state l).sigma ≤ r.runningSigma k := by
  exact Finset.le_sup' (fun i => (r.state i).sigma) (Finset.mem_range.mpr (by omega))

/-- Bounding the actual running maximum is equivalent to bounding every encountered parameter. -/
theorem Execution.runningSigma_le_iff {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {k : ℕ} {B : ℝ} :
    r.runningSigma k ≤ B ↔ ∀ l, l ≤ k → (r.state l).sigma ≤ B := by
  constructor
  · exact fun h l hl => (r.sigma_le_running hl).trans h
  · intro h
    exact Finset.sup'_le _ _ fun l hl => h l (by have := Finset.mem_range.mp hl; omega)

/-- The initial running maximum is exactly the initial regularization parameter. -/
@[simp] theorem Execution.runningSigma_zero {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) : r.runningSigma 0 = (r.state 0).sigma := by
  simp [Execution.runningSigma]

end Optimization.InexactRegularization

namespace Optimization.InexactRegularization
open InexactTaylorModels
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The source radius floor holds with the actual running maximum at each iteration,
without assuming that the printed all-iteration parameter bound is valid. -/
theorem Execution.radii_lower_running {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {L : ℝ} (hL : 1 ≤ L)
    (hA : ∀ k < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i‖ ≤ L)
    {k : ℕ} (hk : k ≤ N) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    P.fraction * P.theta / (24 * max L (r.runningSigma k)) * P.epsilon j ≤
      (r.state k).radii j := by
  exact (r.prefix hk).radii_lower hL (fun l hl => r.sigma_le_running hl)
    (fun l hl => hA l (hl.trans_le hk)) le_rfl hj hjq

/-- The current Step 2 output passes all coefficient checks below the explicit source
request threshold. Its step lower bound follows from the actual retained witness. -/
theorem Execution.stepAccurate_of_uniform_request
    {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {L B : ℝ} (hL : 1 ≤ L)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ B)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i‖ ≤ L)
    (I : Inspection P (f (r.state N).point)
      (oracle (r.state N).point (r.state N).request) (r.state N).sigma (r.state N).radii)
    (hq : I.order ≤ P.q)
    (s : InnerResult P (f (r.state N).point) (oracle (r.state N).point (r.state N).request)
      (r.state N).sigma I.radii (I.direction hq))
    {ε : ℝ} (hε : 0 ≤ ε) (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, (r.state N).request i ≤
      P.kappaStep * (P.fraction * (P.fraction * P.theta / (24 * max L B)) ^ P.q /
        (12 * (P.q ! : ℝ) * max L B)) ^ P.p * ε ^ (P.p * (P.q + 1))) :
    StepAccurate P P.p (r.state N).request s.step := by
  by_cases hs : 1 ≤ ‖s.step‖
  · exact Or.inl hs
  · have hvf := P.fraction_pos
    have hB : 0 < max L B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hcoef : 0 ≤ P.fraction * P.theta / (24 * max L B) := by
      exact div_nonneg (mul_nonneg P.fraction_pos.le P.theta_pos.le) (by positivity)
    have hlo := s.norm_lower I hq hL
      (P.sigmaMin_pos.le.trans (r.sigma_floor le_rfl)) (hA N le_rfl)
      (r.valid_radii le_rfl) hcoef hε (hεj _ I.order_pos hq)
      ((mul_le_mul_of_nonneg_left (hεj _ I.order_pos hq) hcoef).trans
        (r.inspection_radii_lower hL hσ hA I I.order_pos hq)) (le_of_not_ge hs)
    have hM : max L (r.state N).sigma ≤ max L B := max_le_max_left L (hσ N le_rfl)
    have hM0 : 0 < max L (r.state N).sigma :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hlo' : (P.fraction * (P.fraction * P.theta / (24 * max L B)) ^ P.q /
        (12 * (P.q ! : ℝ) * max L B)) * ε ^ (P.q + 1) ≤ ‖s.step‖ := by
      apply le_trans _ hlo
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    apply Optimization.InexactRegularization.stepAccurate_of_uniform_request (by positivity) hlo'
    intro i hi
    convert hh i hi using 1
    rw [mul_pow, ← pow_mul]
    ring

/-- A complete all-pass inspection at a reachable state certifies true quality under the
uniform source accuracy budget and the proved historical radius floor. No radius-floor
premise or stopping-quality premise is supplied by the caller. -/
theorem Execution.true_quality_of_uniform_accuracy
    {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) {L B : ℝ} (hL : 1 ≤ L)
    (hσ : ∀ k, k ≤ N → (r.state k).sigma ≤ B)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i‖ ≤ L)
    (I : Inspection P (f (r.state N).point)
      (oracle (r.state N).point (r.state N).request) (r.state N).sigma (r.state N).radii)
    (hall : I.order = P.q + 1)
    {ε K H : ℝ} (hε : 0 ≤ ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state N).point (r.state N).request i -
        iteratedFDeriv ℝ i f (r.state N).point‖ ≤ K * H)
    (hsmall : 4 * (P.q ! : ℝ) * K * H ≤
      P.fraction * (P.fraction * P.theta / (24 * max L B)) ^ P.q * ε ^ (P.q + 1)) :
    HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
      (r.state N).point I.radii := by
  have hκ : 0 ≤ P.fraction * P.theta / (24 * max L B) := by
    exact div_nonneg (mul_nonneg P.fraction_pos.le P.theta_pos.le)
      (by have := le_max_left L B; positivity)
  apply I.true_quality_of_uniform_accuracy hall (r.valid_radii le_rfl) hκ hε hεj
    (fun j hj hjq => (mul_le_mul_of_nonneg_left (hεj j hj hjq) hκ).trans
      (r.inspection_radii_lower hL hσ hA I hj hjq)) hK hH hcoeff hsmall

end Optimization.InexactRegularization
