import Numlib.Optimization.TrustRegion.HighOrder.Trial

/-!
# Radius and decrease bounds for arbitrary-order trust-region runs

The finite run contains actual trials and initialization. Bounds on initial Taylor
models and the radius are derived from these operational rules. Constants are defined
using only the fixed parameters and initial derivatives, before any accuracy values.
-/

open Set
open scoped BigOperators
namespace HighOrderTrustRegion

/-- The reciprocal factorial sum beginning with `1/1!` is bounded by two. -/
theorem sum_inv_factorial_le_two (q : ℕ) :
    ∑ i ∈ Finset.range q, (1 : ℝ) / (i + 1).factorial ≤ 2 := by
  have hstrong : ∀ n : ℕ, (∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1).factorial) ≤
      2 - 2 / (n + 1).factorial := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hfact : (0 : ℝ) < (n + 1).factorial := by positivity
      have hnext : (((n + 1) + 1).factorial : ℝ) = (n + 2 : ℝ) * (n + 1).factorial := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        push_cast
        ring
      rw [hnext]
      have hfrac : 2 / ((n + 2 : ℝ) * (n + 1).factorial) ≤ 1 / (n + 1).factorial := by
        apply (div_le_div_iff₀ (by positivity) hfact).2
        nlinarith
      calc
        _ ≤ ((2 : ℝ) - 2 / (n + 1).factorial) + 1 / (n + 1).factorial := by linarith
        _ = (2 : ℝ) - 1 / (n + 1).factorial := by ring
        _ ≤ _ := sub_le_sub_left hfrac 2
  exact (hstrong q).trans (sub_le_self _ (by positivity))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonterminal finite run of the exact arbitrary-order trust-region algorithm.
Every trial obeys the actual local algorithm rules; no radius floor or decrease floor
is part of the run predicate. -/
structure Run {q : ℕ} (f : E → ℝ) (P : Parameters q) (x s : ℕ → E)
    (d : ℕ → Fin q → E) (j : ℕ → Fin q) (Δ ρ : ℕ → ℝ) (N : ℕ) : Prop where
  initial_radius_pos : 0 < Δ 0
  initial_radius_le_max : Δ 0 ≤ P.radiusMax
  trials : ∀ i < N, Trial f P (x i) (Δ i) (d i) (j i) (s i) (x (i + 1)) (Δ (i + 1)) (ρ i)

/-- The largest initial derivative norm in equation (12.2.14). -/
noncomputable def initialDerivativeBound (f : E → ℝ) (q : ℕ) (hq : 0 < q) (x : E) : ℝ :=
  Finset.univ.sup' ⟨⟨0,hq⟩, Finset.mem_univ _⟩
    (fun a : Fin q => ‖iteratedFDeriv ℝ (modelOrder a) f x‖)

/-- Each derivative through order `q` is bounded by the actual initial finite maximum. -/
theorem le_initialDerivativeBound (f : E → ℝ) {q : ℕ} (hq : 0 < q) (x : E) (a : Fin q) :
    ‖iteratedFDeriv ℝ (modelOrder a) f x‖ ≤ initialDerivativeBound f q hq x :=
  Finset.le_sup' (fun b : Fin q => ‖iteratedFDeriv ℝ (modelOrder b) f x‖) (Finset.mem_univ a)

/-- A scalar bounds the initial derivative maximum exactly when it bounds every
actual derivative norm through the chosen maximal order. -/
theorem initialDerivativeBound_le_iff (f : E → ℝ) {q : ℕ} (hq : 0 < q) (x : E) (B : ℝ) :
    initialDerivativeBound f q hq x ≤ B ↔
      ∀ a : Fin q, ‖iteratedFDeriv ℝ (modelOrder a) f x‖ ≤ B := by
  constructor
  · intro h a
    exact (le_initialDerivativeBound f hq x a).trans h
  · intro h
    exact Finset.sup'_le _ _ (fun a _ => h a)

/-- The initial finite maximum is nonnegative. -/
theorem initialDerivativeBound_nonneg (f : E → ℝ) {q : ℕ} (hq : 0 < q) (x : E) :
    0 ≤ initialDerivativeBound f q hq x :=
  (norm_nonneg _).trans (le_initialDerivativeBound f hq x ⟨0,hq⟩)

/-- The initial Taylor decrement is bounded by twice the largest derivative norm on
a ball of radius at most one. -/
theorem decrement_le_two_derivativeBound (f : E → ℝ) {q : ℕ} (hq : 0 < q)
    (x : E) (a : Fin q) {δ : ℝ} (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {d : E} (hd : ‖d‖ ≤ δ) :
    TaylorModel.decrement f (modelOrder a) x d ≤ 2 * initialDerivativeBound f q hq x := by
  let B := initialDerivativeBound f q hq x
  have hB : 0 ≤ B := initialDerivativeBound_nonneg f hq x
  have heq : TaylorModel.decrement f (modelOrder a) x d =
      -(∑ i ∈ Finset.range (a.val + 1),
        (((i + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (i + 1) f x (fun _ => d)) := by
    rw [TaylorModel.decrement_eq, TaylorModel.eval_eq_sum]
    dsimp [modelOrder]
    rw [Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedFDeriv_zero_apply,
      ]
    ring
  have hterm (i : ℕ) (hi : i ∈ Finset.range (a.val + 1)) :
      |(((i + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (i + 1) f x (fun _ => d)| ≤
        B * ((1 : ℝ) / (i + 1).factorial) := by
    have hiq : i < q := (Finset.mem_range.mp hi).trans_le (Nat.succ_le_of_lt a.isLt)
    have hiB := le_initialDerivativeBound f hq x ⟨i,hiq⟩
    have hn := (iteratedFDeriv ℝ (i + 1) f x).le_opNorm (fun _ => d)
    simp only [Fin.prod_const, Real.norm_eq_abs] at hn
    have hpow : ‖d‖ ^ (i + 1) ≤ 1 := pow_le_one₀ (norm_nonneg d) (hd.trans hδ1)
    have hv : |iteratedFDeriv ℝ (i + 1) f x (fun _ => d)| ≤ B :=
      hn.trans ((mul_le_of_le_one_right (norm_nonneg _) hpow).trans hiB)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((i + 1).factorial : ℝ)⁻¹)]
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hv
      (by positivity : (0 : ℝ) ≤ ((i + 1).factorial : ℝ)⁻¹)
  rw [heq]
  calc -(∑ i ∈ Finset.range (a.val + 1),
        (((i + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (i + 1) f x (fun _ => d)) ≤
      |∑ i ∈ Finset.range (a.val + 1),
        (((i + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (i + 1) f x (fun _ => d)| := neg_le_abs _
    _ ≤ ∑ i ∈ Finset.range (a.val + 1),
        |(((i + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (i + 1) f x (fun _ => d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (a.val + 1), B * ((1 : ℝ) / (i + 1).factorial) :=
      Finset.sum_le_sum hterm
    _ = B * ∑ i ∈ Finset.range (a.val + 1), (1 : ℝ) / (i + 1).factorial :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_inv_factorial_le_two _) hB
    _ = _ := mul_comm _ _

/-- The exact source radius coefficient. The printed `2q!` is the product `2 · q!`,
coming from the reciprocal-factorial sum bound. No accuracy is an argument. -/
noncomputable def radiusConstant (f : E → ℝ) (q : ℕ) (hq : 0 < q) (x₀ : E)
    (Δ₀ theta eta2 gamma1 L : ℝ) : ℝ :=
  gamma1 * (1 - eta2) / L * min theta
    (Δ₀ * (min Δ₀ theta) ^ q / (2 * (q.factorial : ℝ) * initialDerivativeBound f q hq x₀))

/-- The smallest accuracy among orders `1, …, q`. -/
noncomputable def minimumAccuracy {q : ℕ} (P : Parameters q) : ℝ :=
  Finset.univ.inf' ⟨⟨0,P.order_pos⟩, Finset.mem_univ _⟩ P.accuracy

/-- Every accuracy is at least the finite minimum. -/
theorem minimumAccuracy_le {q : ℕ} (P : Parameters q) (a : Fin q) :
    minimumAccuracy P ≤ P.accuracy a := Finset.inf'_le P.accuracy (Finset.mem_univ a)

/-- A scalar is below the minimum accuracy exactly when it is below every accuracy. -/
theorem le_minimumAccuracy_iff {q : ℕ} (P : Parameters q) (a : ℝ) :
    a ≤ minimumAccuracy P ↔ ∀ j, a ≤ P.accuracy j := by
  constructor
  · intro h j
    exact h.trans (minimumAccuracy_le P j)
  · intro h
    exact Finset.le_inf' _ _ (fun j _ => h j)

/-- The finite minimum of the positive source accuracies is positive. -/
theorem minimumAccuracy_pos {q : ℕ} (P : Parameters q) : 0 < minimumAccuracy P := by
  exact (Finset.lt_inf'_iff _).2 (fun a _ => P.accuracy_pos a)

/-- The source optimality-radius cap is at least the smallest accuracy. -/
theorem minimumAccuracy_le_theta {q : ℕ} (P : Parameters q) : minimumAccuracy P ≤ P.theta := by
  obtain ⟨a,ha⟩ := P.min_accuracy_le_theta
  exact (minimumAccuracy_le P a).trans ha

/-- The genuine minimum of the scaled computed Taylor gaps through index `k`. -/
noncomputable def prefixGap {q : ℕ} (f : E → ℝ) (P : Parameters q)
    (x : ℕ → E) (Δ : ℕ → ℝ) (d : ℕ → Fin q → E) (j : ℕ → Fin q) (k : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : Fin (k + 1) => scaledGap f P (x a) (Δ a) (d a) (j a))

/-- Every actual gap in a prefix is at least its minimum. -/
theorem prefixGap_le {q : ℕ} (f : E → ℝ) (P : Parameters q)
    (x : ℕ → E) (Δ : ℕ → ℝ) (d : ℕ → Fin q → E) (j : ℕ → Fin q)
    {k i : ℕ} (hi : i ≤ k) : prefixGap f P x Δ d j k ≤ scaledGap f P (x i) (Δ i) (d i) (j i) :=
  Finset.inf'_le (fun a : Fin (k + 1) => scaledGap f P (x a) (Δ a) (d a) (j a))
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (k + 1)))

/-- A scalar bounds the prefix minimum from below exactly when it bounds each
actual scaled gap in that finite prefix. -/
theorem le_prefixGap_iff {q : ℕ} (f : E → ℝ) (P : Parameters q)
    (x : ℕ → E) (Δ : ℕ → ℝ) (d : ℕ → Fin q → E) (j : ℕ → Fin q) (k : ℕ) (a : ℝ) :
    a ≤ prefixGap f P x Δ d j k ↔
      ∀ i ≤ k, a ≤ scaledGap f P (x i) (Δ i) (d i) (j i) := by
  constructor
  · intro h i hi
    exact h.trans (prefixGap_le f P x Δ d j hi)
  · intro h
    apply Finset.le_inf' _ _
    intro i _
    exact h i (by have := i.isLt; omega)

namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Parameters q} {x s : ℕ → E}
  {d : ℕ → Fin q → E} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N : ℕ}

/-- Every selected gap before termination is at least the tolerance for that order. -/
theorem scaledGap_ge (h : Run f P x s d j Δ ρ N) {i : ℕ} (hi : i < N) :
    P.zeta * P.accuracy (j i) ≤ scaledGap f P (x i) (Δ i) (d i) (j i) :=
  ModelDecrease.le_scaled_of_test _ (h.trials i hi).optimalityRadius_pos (h.trials i hi).failed_test

/-- A genuine initial nonterminal trial makes the initial derivative maximum positive. -/
theorem initialDerivativeBound_pos (h : Run f P x s d j Δ ρ N) (hN : 0 < N) :
    0 < initialDerivativeBound f q P.order_pos (x 0) := by
  have ht := h.trials 0 hN
  have hb := decrement_le_two_derivativeBound f P.order_pos (x 0) (j 0)
    ht.optimalityRadius_pos.le (min_le_right _ _ |>.trans P.theta_le_one)
    (ht.direction_feasible _ le_rfl)
  linarith [ht.direction_decrement_pos]

/-- Initial scaled gap estimate, derived from the actual Taylor polynomial. -/
theorem initial_scaledGap_le (h : Run f P x s d j Δ ρ N) (hN : 0 < N) :
    scaledGap f P (x 0) (Δ 0) (d 0) (j 0) ≤
      2 * (q.factorial : ℝ) * initialDerivativeBound f q P.order_pos (x 0) /
        optimalityRadius P (Δ 0) ^ q := by
  have ht := h.trials 0 hN
  have hδ := ht.optimalityRadius_pos
  have hδ1 : optimalityRadius P (Δ 0) ≤ 1 :=
    (optimalityRadius_le_theta P _).trans P.theta_le_one
  have hb := decrement_le_two_derivativeBound f P.order_pos (x 0) (j 0) hδ.le hδ1
    (ht.direction_feasible _ le_rfl)
  have hf : ((modelOrder (j 0)).factorial : ℝ) ≤ q.factorial := by
    exact_mod_cast Nat.factorial_le (modelOrder_le (j 0))
  have hp : optimalityRadius P (Δ 0) ^ q ≤ optimalityRadius P (Δ 0) ^ modelOrder (j 0) :=
    pow_le_pow_of_le_one hδ.le hδ1 (modelOrder_le (j 0))
  have hB := initialDerivativeBound_nonneg f P.order_pos (x 0)
  unfold scaledGap ModelDecrease.scaled
  apply (div_le_div_iff₀ (pow_pos hδ _) (pow_pos hδ _)).2
  have hmul := mul_le_mul hb hf (by positivity : (0 : ℝ) ≤ (modelOrder (j
    0)).factorial) (by positivity : (0 : ℝ) ≤ 2 * initialDerivativeBound f q
    P.order_pos (x 0))
  have hmul' := mul_le_mul_of_nonneg_right hmul (pow_nonneg hδ.le q)
  have hpow' := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ 2 * (q.factorial : ℝ) * initialDerivativeBound f q P.order_pos (x 0))
  nlinarith

/-- The run's prefix minimum retains the actual failing-test tolerance lower bound. -/
theorem prefixGap_ge (h : Run f P x s d j Δ ρ N) {k : ℕ} (hk : k < N) :
    P.zeta * minimumAccuracy P ≤ prefixGap f P x Δ d j k := by
  apply (Finset.le_inf'_iff _ _).2
  intro a _
  exact (mul_le_mul_of_nonneg_left (minimumAccuracy_le P (j a)) P.zeta_pos.le).trans
    (h.scaledGap_ge (by have := a.isLt; omega))

/-- Every actual prefix minimum before termination is positive. -/
theorem prefixGap_pos (h : Run f P x s d j Δ ρ N) {k : ℕ} (hk : k < N) :
    0 < prefixGap f P x Δ d j k :=
  (mul_pos P.zeta_pos (minimumAccuracy_pos P)).trans_le (h.prefixGap_ge hk)

/-- Each actual radius update contracts by at most the allowed factor `γ₁`. -/
theorem gamma1_mul_radius_le (h : Run f P x s d j Δ ρ N) {i : ℕ} (hi : i < N) :
    P.gamma1 * Δ i ≤ Δ (i + 1) := by
  have ht := h.trials i hi
  have hu := ht.radius_update
  have hγ : P.gamma1 ≤ 1 := P.gamma1_le_gamma2.trans P.gamma2_lt_one.le
  split_ifs at hu
  · exact (mul_le_of_le_one_left ht.radius_pos.le hγ).trans hu.1
  · exact (mul_le_mul_of_nonneg_right P.gamma1_le_gamma2 ht.radius_pos.le).trans hu.1
  · exact hu.1

/-- A proved small-radius acceptance condition yields a uniform finite-prefix floor.
The condition is a premise of this update lemma, not a field of the operational run. -/
theorem min_initial_threshold_le (h : Run f P x s d j Δ ρ N) {threshold : ℝ}
    (hgood : ∀ i < N, Δ i < threshold → P.eta2 ≤ ρ i) {i : ℕ} (hi : i ≤ N) :
    min (Δ 0) (P.gamma1 * threshold) ≤ Δ i := by
  induction i with
  | zero => exact min_le_left _ _
  | succ i ih =>
    by_cases hs : Δ i < threshold
    · exact (ih (by omega)).trans
        ((h.trials i (by omega)).radius_le_next_of_very_successful (hgood i (by omega) hs))
    · exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_gt hs) P.gamma1_pos.le).trans
          (h.gamma1_mul_radius_le (by omega)))

/-- The exact source radius coefficient is positive and smaller than `γ₁`. -/
theorem radiusConstant_pos_lt_gamma1 (h : Run f P x s d j Δ ρ N) (hN : 0 < N)
    {L : ℝ} (hL : 1 ≤ L) :
    0 < radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L ∧
      radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L < P.gamma1 := by
  have hB := h.initialDerivativeBound_pos hN
  have hδ := (h.trials 0 hN).optimalityRadius_pos
  have hLp : 0 < L := by linarith
  have hηp : 0 < 1 - P.eta2 := by linarith [P.eta2_lt_one]
  have hη0 : 0 < P.eta2 := P.eta1_pos.trans_le P.eta1_le_eta2
  have hc : 0 < P.gamma1 * (1 - P.eta2) / L := div_pos (mul_pos P.gamma1_pos hηp) hLp
  have hclt : P.gamma1 * (1 - P.eta2) / L < P.gamma1 := by
    apply (div_lt_iff₀ hLp).2
    nlinarith [P.gamma1_pos]
  have hmpos : 0 < min P.theta
      (Δ 0 * min (Δ 0) P.theta ^ q /
        (2 * (q.factorial : ℝ) * initialDerivativeBound f q P.order_pos (x 0))) := by
    apply lt_min P.theta_pos
    exact div_pos (mul_pos h.initial_radius_pos (pow_pos hδ _)) (by positivity)
  unfold radiusConstant
  exact ⟨mul_pos hc hmpos, (mul_le_of_le_one_right hc.le
    ((min_le_left _ _).trans P.theta_le_one)).trans_lt hclt⟩

/-- The initial actual gap times the fixed radius coefficient is at most the initial radius. -/
theorem radiusConstant_mul_initialGap_le (h : Run f P x s d j Δ ρ N) (hN : 0 < N)
    {L : ℝ} (hL : 1 ≤ L) :
    radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L *
      scaledGap f P (x 0) (Δ 0) (d 0) (j 0) ≤ Δ 0 := by
  let B := initialDerivativeBound f q P.order_pos (x 0)
  let δ := optimalityRadius P (Δ 0)
  let c := P.gamma1 * (1 - P.eta2) / L
  have hB : 0 < B := h.initialDerivativeBound_pos hN
  have hδ : 0 < δ := (h.trials 0 hN).optimalityRadius_pos
  have hLp : 0 < L := by linarith
  have hc : 0 < c := by dsimp [c]; positivity [P.gamma1_pos, P.eta2_lt_one]
  have hη0 := P.eta1_pos.trans_le P.eta1_le_eta2
  have hγ : P.gamma1 < 1 := P.gamma1_le_gamma2.trans_lt P.gamma2_lt_one
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ hLp).2
    nlinarith [P.gamma1_pos]
  have hb := h.initial_scaledGap_le hN
  have hgap := (h.trials 0 hN).scaledGap_pos
  have hκ : radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L ≤
      c * (Δ 0 * δ ^ q / (2 * (q.factorial : ℝ) * B)) := by
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
  calc
    _ ≤ (c * (Δ 0 * δ ^ q / (2 * (q.factorial : ℝ) * B))) *
        (2 * (q.factorial : ℝ) * B / δ ^ q) :=
      mul_le_mul hκ hb hgap.le
        (mul_nonneg hc.le (div_nonneg
          (mul_nonneg h.initial_radius_pos.le (pow_nonneg hδ.le _)) (by positivity)))
    _ = c * Δ 0 := by field_simp
    _ ≤ Δ 0 := mul_le_of_le_one_left h.initial_radius_pos.le hc1

/-- Restrict a genuine run to an earlier finite prefix. -/
theorem restrict (h : Run f P x s d j Δ ρ N) {M : ℕ} (hM : M ≤ N) :
    Run f P x s d j Δ ρ M :=
  ⟨h.initial_radius_pos, h.initial_radius_le_max, fun i hi => h.trials i (hi.trans_le hM)⟩

/-- The exact uniform prefix radius lower bound (12.2.13). -/
theorem radius_lower (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) :
    min (P.gamma1 * P.theta)
      (radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L *
        prefixGap f P x Δ d j k) ≤ Δ k := by
  let κ := radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
  let m := prefixGap f P x Δ d j k
  let c := (1 - P.eta2) / L
  have hN : 0 < N := by omega
  have hκ := (h.radiusConstant_pos_lt_gamma1 hN hL).1
  have hm : 0 < m := h.prefixGap_pos hk
  have hLp : 0 < L := by linarith
  have hc : 0 < c := div_pos (by linarith [P.eta2_lt_one]) hLp
  have hfloor : min (Δ 0) (P.gamma1 * min P.theta (c * m)) ≤ Δ k := by
    apply (h.restrict hk.le).min_initial_threshold_le (i := k) _ le_rfl
    intro i hi hsmall
    have ht := h.trials i (hi.trans hk)
    apply (ht.very_successful hf hLp (hlip (j i)) _).1
    apply le_min
    · exact hsmall.le.trans (min_le_left _ _)
    · calc
        Δ i ≤ c * m := hsmall.le.trans (min_le_right _ _)
        _ ≤ c * scaledGap f P (x i) (Δ i) (d i) (j i) :=
          mul_le_mul_of_nonneg_left (prefixGap_le f P x Δ d j (by omega)) hc.le
  have hinit : min (P.gamma1 * P.theta) (κ * m) ≤ Δ 0 := by
    calc
      _ ≤ κ * m := min_le_right _ _
      _ ≤ κ * scaledGap f P (x 0) (Δ 0) (d 0) (j 0) :=
        mul_le_mul_of_nonneg_left (prefixGap_le f P x Δ d j (by omega)) hκ.le
      _ ≤ Δ 0 := h.radiusConstant_mul_initialGap_le hN hL
  have hκbound : κ ≤ P.gamma1 * c := by
    have hfactor : 0 ≤ P.gamma1 * (1 - P.eta2) / L :=
      div_nonneg (mul_nonneg P.gamma1_pos.le (by linarith [P.eta2_lt_one])) hLp.le
    have hh := mul_le_of_le_one_right hfactor
      ((min_le_left P.theta
        (Δ 0 * min (Δ 0) P.theta ^ q /
          (2 * (q.factorial : ℝ) * initialDerivativeBound f q P.order_pos (x
            0)))).trans P.theta_le_one)
    exact hh.trans_eq (by dsimp [c]; ring)
  have hstep : min (P.gamma1 * P.theta) (κ * m) ≤ P.gamma1 * min P.theta (c * m) := by
    by_cases hcθ : P.theta ≤ c * m
    · rw [min_eq_left hcθ]
      exact min_le_left _ _
    · rw [min_eq_right (le_of_not_ge hcθ)]
      calc
        _ ≤ κ * m := min_le_right _ _
        _ ≤ (P.gamma1 * c) * m := mul_le_mul_of_nonneg_right hκbound hm.le
        _ = _ := by ring
  exact (le_min hinit hstep).trans hfloor

/-- The actual optimality radius and scaled gap have a common fixed lower bound. -/
theorem radius_gap_lower (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) :
    let κ := radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
    let b := P.zeta * κ * minimumAccuracy P
    b ≤ optimalityRadius P (Δ k) ∧ b ≤ scaledGap f P (x k) (Δ k) (d k) (j k) ∧
      0 < b ∧ b ≤ 1 := by
  let κ := radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
  let ε := minimumAccuracy P
  let b := P.zeta * κ * ε
  have hκ := h.radiusConstant_pos_lt_gamma1 (by omega) hL
  have hκ0 : 0 < κ := hκ.1
  have hκγ : κ < P.gamma1 := hκ.2
  have hγ1 : P.gamma1 < 1 := P.gamma1_le_gamma2.trans_lt P.gamma2_lt_one
  have hκ1 : κ ≤ 1 := hκγ.le.trans hγ1.le
  have hε : 0 < ε := minimumAccuracy_pos P
  have hεθ : ε ≤ P.theta := minimumAccuracy_le_theta P
  have hb0 : 0 < b := mul_pos (mul_pos P.zeta_pos hκ0) hε
  have hbε : b ≤ ε := by
    have hh : P.zeta * κ ≤ 1 := (mul_le_of_le_one_left hκ0.le P.zeta_le_one).trans hκ1
    exact mul_le_of_le_one_left hε.le hh
  have hbθ : b ≤ P.theta := hbε.trans hεθ
  have hbγθ : b ≤ P.gamma1 * P.theta := by
    calc
      b ≤ κ * ε := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hκ0.le P.zeta_le_one) hε.le
      _ ≤ P.gamma1 * P.theta := mul_le_mul hκγ.le hεθ hε.le P.gamma1_pos.le
  have hbm : b ≤ κ * prefixGap f P x Δ d j k := by
    have hh := mul_le_mul_of_nonneg_left (h.prefixGap_ge hk) hκ0.le
    dsimp [b]
    nlinarith
  have hbΔ : b ≤ Δ k := (le_min hbγθ hbm).trans (h.radius_lower hf hL hlip hk)
  have hgap : b ≤ scaledGap f P (x k) (Δ k) (d k) (j k) := by
    calc
      b = κ * (P.zeta * ε) := by dsimp [b]; ring
      _ ≤ P.zeta * ε := mul_le_of_le_one_left (mul_nonneg P.zeta_pos.le hε.le) hκ1
      _ ≤ _ := (mul_le_mul_of_nonneg_left (minimumAccuracy_le P (j k)) P.zeta_pos.le).trans
        (h.scaledGap_ge hk)
  exact ⟨le_min hbΔ hbθ, hgap, hb0, hbθ.trans P.theta_le_one⟩

/-- The exact source model-decrease floor (12.2.18) follows from the actual computed
Taylor gap and the proved radius floor. -/
theorem model_decrease (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) :
    (P.zeta * radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L) ^ (q + 1) /
      q.factorial * minimumAccuracy P ^ (q + 1) ≤
        TaylorModel.decrement f (modelOrder (j k)) (x k) (s k) := by
  let κ := radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
  let b := P.zeta * κ * minimumAccuracy P
  obtain ⟨hbδ,hbg,hb0,hb1⟩ := h.radius_gap_lower hf hL hlip hk
  have ht := h.trials k hk
  have hm := ht.scaledGap_le_decrement
  have hjq := modelOrder_le (j k)
  have hfp : (0 : ℝ) < (modelOrder (j k)).factorial := by positivity
  have hfq : (0 : ℝ) < q.factorial := by positivity
  have hfjq : ((modelOrder (j k)).factorial : ℝ) ≤ q.factorial := by
    exact_mod_cast Nat.factorial_le hjq
  have hp : b ^ (q + 1) ≤ b ^ (modelOrder (j k) + 1) :=
    pow_le_pow_of_le_one hb0.le hb1 (Nat.succ_le_succ hjq)
  have hpδ : b ^ modelOrder (j k) ≤ optimalityRadius P (Δ k) ^ modelOrder (j k) :=
    pow_le_pow_left₀ hb0.le hbδ _
  have hbd : b ^ (q + 1) / (q.factorial : ℝ) ≤
      TaylorModel.decrement f (modelOrder (j k)) (x k) (s k) := by
    calc
      _ ≤ b ^ (modelOrder (j k) + 1) / (q.factorial : ℝ) :=
        div_le_div_of_nonneg_right hp hfq.le
      _ ≤ b ^ (modelOrder (j k) + 1) / ((modelOrder (j k)).factorial : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg hb0.le _) hfp hfjq
      _ = b * b ^ modelOrder (j k) / ((modelOrder (j k)).factorial : ℝ) := by rw [pow_succ]; ring
      _ ≤ scaledGap f P (x k) (Δ k) (d k) (j k) *
          optimalityRadius P (Δ k) ^ modelOrder (j k) / ((modelOrder (j k)).factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hbg hpδ (pow_nonneg hb0.le _) ht.scaledGap_pos.le) hfp.le
      _ ≤ _ := hm
  convert hbd using 1
  dsimp [b]
  rw [mul_pow]
  ring

/-- Every accepted actual trial attains the source objective decrease (12.2.19). -/
theorem function_decrease (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (hs : P.eta1 ≤ ρ k) :
    P.eta1 * (P.zeta * radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2
      P.gamma1 L) ^ (q + 1) /
      q.factorial * minimumAccuracy P ^ (q + 1) ≤ f (x k) - f (x (k + 1)) := by
  have ht := h.trials k hk
  have hd := mul_le_mul_of_nonneg_left (h.model_decrease hf hL hlip hk) P.eta1_pos.le
  have ha : P.eta1 * TaylorModel.decrement f (modelOrder (j k)) (x k) (s k) ≤
      f (x k) - f (x k + s k) := by
    rw [ht.ratio] at hs
    exact (le_div_iff₀ ht.denominator_pos).1 hs
  rw [ht.point_update, ite_eq_left hs]
  convert hd.trans ha using 1
  ring

end Run
end HighOrderTrustRegion
