import Numlib.Optimization.Regularization.HighOrder.Sharpness.Model
import Numlib.Optimization.Regularization.HighOrder.Run
import Numlib.Optimization.Regularization.HighOrder.EmptyDirections
import Numlib.Optimization.Sharpness.Curvature

/-!
# Actual finite regularization executions from monomial jets

The objective's actual derivatives yield first-, second- and third-order finite
runs. All trial models, ratios, least Hessian eigenpairs and inherited direction
sets are genuine. Every terminal derivative satisfies the requested tolerance,
and the terminal direction set is nonempty. Objective bounds and highest-derivative
Lipschitz constants are uniform before all accuracies and tested orders.
-/

open Set
namespace HighOrderRegularization.Sharpness

/-- The exact inverse-accuracy trial count. -/
noncomputable def length (p r : ℕ) (ε : ℝ) : ℕ := horizon p (root p r ε)

/-- The actual interpolation grid at the scaled stationary step. -/
noncomputable def iterate (p r : ℕ) (ε : ℝ) (k : ℕ) : ℝ := point (step p r ε) k

/-- Initial directions use the objective; later directions are all scalar unit vectors. -/
noncomputable def directions (f : ℝ → ℝ) (p r : ℕ) (ε ε₂ : ℝ) (k : ℕ) : Set ℝ :=
  if k = 0 then initialDirections f (iterate p r ε 0) ε₂ else {v | ‖v‖ = 1}

/-- Every matched positive derivative has exactly its requested accuracy scaling. -/
theorem derivative_eq_accuracy {f : ℝ → ℝ} {p r k j : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : MatchesJets f p r (length p r ε) (amplitude p r) (step p r ε))
    (hk : k ≤ length p r ε) (hj : 0 < j) (hjp : j ≤ p) :
    iteratedDeriv j f (iterate p r ε k) =
      if j = r then -(if k < length p r ε then 2 else 1) * ε else 0 := by
  rw [iterate, h k hk j hjp]
  by_cases hjr : j = r
  · subst j
    simp only [jet, ite_eq_right (Nat.ne_of_gt hj), ite_true]
    have hh := amplitude_step_power (p := p) (r := r) hε
    by_cases hkN : k < length p r ε
    · rw [ite_eq_left hkN, ite_eq_left hkN]
      linarith
    · rw [ite_eq_right hkN, ite_eq_right hkN]
      linarith
  · simp [jet, Nat.ne_of_gt hj, hjr]

/-- The first derivative norm is the actual scalar first derivative norm. -/
theorem first_norm_eq_accuracy {f : ℝ → ℝ} {p r k : ℕ} {ε : ℝ}
    (hp : 1 ≤ p) (hε : 0 ≤ ε)
    (h : MatchesJets f p r (length p r ε) (amplitude p r) (step p r ε))
    (hk : k ≤ length p r ε) :
    ‖fderiv ℝ f (iterate p r ε k)‖ =
      if r = 1 then (if k < length p r ε then 2 else 1) * ε else 0 := by
  rw [← norm_deriv_eq_norm_fderiv, ← iteratedDeriv_one,
    derivative_eq_accuracy hε h hk (by norm_num) hp]
  by_cases hr : r = 1
  · subst r
    by_cases hkN : k < length p 1 ε <;>
      simp [hkN, Real.norm_eq_abs, abs_of_nonneg hε]
  · simp [hr, Ne.symm hr]

/-- The actual Hessian least eigenpair in one real dimension. -/
theorem leastEigenpair (f : ℝ → ℝ) (p r k : ℕ) (ε : ℝ) :
    SecondOrderTrustRegion.IsLeastEigenpair f (iterate p r ε k)
      (iteratedDeriv 2 f (iterate p r ε k)) 1 := CurvatureSharpness.leastEigenpair _ _

/-- Actual second and third tensor values have the scalar accuracy magnitude on unit directions. -/
theorem directional_abs_eq_accuracy {f : ℝ → ℝ} {p r k j : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : MatchesJets f p r (length p r ε) (amplitude p r) (step p r ε))
    (hk : k ≤ length p r ε) (hj : 0 < j) (hjp : j ≤ p)
    (v : ℝ) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ j f (iterate p r ε k) (fun _ => v)| =
      if j = r then (if k < length p r ε then 2 else 1) * ε else 0 := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_const, smul_eq_mul,
    abs_mul, abs_pow, show |v| = 1 by exact hv, one_pow, one_mul,
    derivative_eq_accuracy hε h hk hj hjp]
  by_cases hjr : j = r
  · by_cases hkN : k < length p r ε <;>
      simp [hjr, hkN, abs_of_nonneg hε]
  · simp [hjr]

/-- Every post-initial inherited set is nonempty, with both scalar unit directions. -/
theorem directions_succ (f : ℝ → ℝ) (p r : ℕ) (ε ε₂ : ℝ) (k : ℕ) :
    directions f p r ε ε₂ (k + 1) = {v | ‖v‖ = 1} := by simp [directions]

/-- The chosen inherited sets are exactly the actual model small-curvature sets. -/
theorem directions_update {f : ℝ → ℝ} {p r k : ℕ} {ε ε₂ : ℝ}
    (hp : 2 ≤ p) (hr : 0 < r) (hrp : r ≤ p) (hε : 0 < ε)
    (h : MatchesJets f p r (length p r ε) (amplitude p r) (step p r ε))
    (hk : k < length p r ε) :
    directions f p r ε ε₂ (k + 1) =
      smallModelDirections f p (iterate p r ε k) (step p r ε) (parameter p) 1 := by
  rw [directions_succ]
  exact (smallModelDirections_eq hp hr hrp h hk (step_pos p r hε)).symm

/-- A first-order witness follows the full branch with both higher tests disabled. -/
theorem firstOrderRun_of_matches {f : ℝ → ℝ} {p : ℕ} (hp : 1 ≤ p) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : MatchesJets f p 1 (length p 1 ε) (amplitude p 1) (step p 1 ε)) :
    FirstOrderRun f p (iterate p 1 ε) (fun _ => step p 1 ε)
      (fun _ => parameter p) (fun _ => 1)
      (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 ε ⊤ ⊤ (length p 1 ε) where
  trace := modelTrace_of_matches (by norm_num) hp h (step_pos p 1 hε)
  second_order_disabled := rfl
  third_order_disabled := rfl
  theta_first_pos := by norm_num
  theta_first_le_one := le_rfl
  accuracy_first_pos := hε
  accuracy_first_le_one := hε1
  not_terminated := by
    intro k hk
    rw [first_norm_eq_accuracy hp hε.le h hk.le]
    simp only [ite_true, ite_eq_left hk]
    linarith
  stationary_first := fun k hk => model_first_test (by norm_num) hp h hk (step_pos p 1 hε)

/-- Accuracy attached to the derivative order that determines a slow branch. -/
def selectedAccuracy (r : ℕ) (ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  if r = 1 then ε₁ else if r = 2 then ε₂ else ε₃

/-- Selecting any of the three source orders preserves positive accuracy. -/
theorem selectedAccuracy_pos (r : ℕ) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    0 < selectedAccuracy r ε₁ ε₂ ε₃ := by
  unfold selectedAccuracy
  split_ifs <;> assumption

/-- Selecting any source order preserves the unit upper accuracy bound. -/
theorem selectedAccuracy_le_one (r : ℕ) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : ε₁ ≤ 1) (h₂ : ε₂ ≤ 1) (h₃ : ε₃ ≤ 1) :
    selectedAccuracy r ε₁ ε₂ ε₃ ≤ 1 := by
  unfold selectedAccuracy
  split_ifs <;> assumption

/-- Either first- or second-order slow data follows the full finite-second-order branch. -/
theorem secondOrderRun_of_matches {f : ℝ → ℝ} {p r : ℕ}
    (hp : 2 ≤ p) (hr : 0 < r) (hr2 : r ≤ 2) {ε₁ ε₂ : ℝ}
    (h₁ : 0 < ε₁) (h₁1 : ε₁ ≤ 1) (h₂ : 0 < ε₂) (h₂1 : ε₂ ≤ 1)
    (h : MatchesJets f p r
      (length p r (selectedAccuracy r ε₁ ε₂ 1)) (amplitude p r)
      (step p r (selectedAccuracy r ε₁ ε₂ 1))) :
    let ε := selectedAccuracy r ε₁ ε₂ 1
    SecondOrderRun f p (iterate p r ε) (fun _ => step p r ε) (fun _ => 1)
      (fun k => iteratedDeriv 2 f (iterate p r ε k))
      (fun _ => parameter p) (fun _ => 1)
      (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 1 ε₁ ε₂ ⊤ (length p r ε) := by
  generalize he : selectedAccuracy r ε₁ ε₂ 1 = ε at *
  have hε : 0 < ε := he ▸ selectedAccuracy_pos r h₁ h₂ (by norm_num)
  have hrp : r ≤ p := hr2.trans hp
  refine ⟨modelTrace_of_matches hr hrp h (step_pos p r hε), hp, rfl,
    by norm_num, le_rfl, by norm_num, le_rfl, h₁, h₁1, h₂, h₂1,
    fun k _ => leastEigenpair f p r k ε, ?_, ?_, ?_⟩
  · intro k hk
    interval_cases r
    · left
      have he : ε = ε₁ := by simpa [selectedAccuracy] using he.symm
      rw [first_norm_eq_accuracy (by omega) hε.le h hk.le]
      simp only [ite_true, ite_eq_left hk]
      rw [he]
      linarith
    · right
      rw [derivative_eq_accuracy hε.le h hk.le (by norm_num) hp]
      simp only [ite_true, ite_eq_left hk]
      have he : ε = ε₂ := by simpa [selectedAccuracy] using he.symm
      rw [he]
      linarith
  · intro k hk
    exact model_first_test hr hrp h hk (step_pos p r hε)
  · intro k hk v hv
    exact model_second_test hp hr hrp h hk (step_pos p r hε) v hv

/-- The third-order witness has a scalar unit direction even before its first trial. -/
theorem one_mem_directions_third {f : ℝ → ℝ} {p k : ℕ} {ε ε₂ : ℝ}
    (hp : 3 ≤ p) (hε : 0 ≤ ε) (h₂ : 0 ≤ ε₂)
    (h : MatchesJets f p 3 (length p 3 ε) (amplitude p 3) (step p 3 ε)) :
    (1 : ℝ) ∈ directions f p 3 ε ε₂ k := by
  by_cases hk : k = 0
  · subst k
    simp only [directions, ite_true, initialDirections, mem_ofPred_eq]
    refine ⟨by norm_num, ?_⟩
    rw [directional_abs_eq_accuracy hε h (by omega : 0 ≤ length p 3 ε)
      (by norm_num) (by omega) 1 (by norm_num)]
    simpa using h₂
  · simp [directions, hk]

/-- All three slow derivative orders follow the actual finite-third-order model and update trace. -/
theorem finiteRun_of_matches {f : ℝ → ℝ} {p r : ℕ}
    (hp : 3 ≤ p) (hr : 0 < r) (hr3 : r ≤ 3) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₁1 : ε₁ ≤ 1) (h₂ : 0 < ε₂) (h₂1 : ε₂ ≤ 1)
    (h₃ : 0 < ε₃) (h₃1 : ε₃ ≤ 1)
    (h : MatchesJets f p r
      (length p r (selectedAccuracy r ε₁ ε₂ ε₃)) (amplitude p r)
      (step p r (selectedAccuracy r ε₁ ε₂ ε₃))) :
    let ε := selectedAccuracy r ε₁ ε₂ ε₃
    FiniteRun f p (iterate p r ε) (fun _ => step p r ε) (fun _ => 1)
      (fun k => iteratedDeriv 2 f (iterate p r ε k))
      (fun _ => parameter p) (fun _ => 1) (directions f p r ε ε₂)
      (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 1 1 ε₁ ε₂ ε₃ (length p r ε) := by
  generalize he : selectedAccuracy r ε₁ ε₂ ε₃ = ε at *
  have hε : 0 < ε := he ▸ selectedAccuracy_pos r h₁ h₂ h₃
  have hrp : r ≤ p := hr3.trans hp
  refine ⟨modelTrace_of_matches hr hrp h (step_pos p r hε), hp,
    by norm_num, le_rfl, by norm_num, le_rfl, by norm_num, le_rfl,
    h₁, h₁1, h₂, h₂1, h₃, h₃1,
    fun k _ => leastEigenpair f p r k ε, by simp [directions],
    fun k hk => directions_update (by omega) hr hrp hε h hk, ?_, ?_⟩
  · intro k hk hs
    have hg := hs.1
    interval_cases r
    · have he : ε = ε₁ := by simpa [selectedAccuracy] using he.symm
      rw [first_norm_eq_accuracy (by omega) hε.le h hk.le] at hg
      simp only [ite_true, ite_eq_left hk] at hg
      rw [he] at hg
      linarith
    · have he : ε = ε₂ := by simpa [selectedAccuracy] using he.symm
      have hh := derivative_eq_accuracy hε.le h hk.le (j := 2) (by norm_num) (by omega)
      simp only [ite_true, ite_eq_left hk] at hh
      rcases hs.2 with hs | hs
      · linarith
      · linarith [hs.1]
    · have he : ε = ε₃ := by simpa [selectedAccuracy] using he.symm
      have hh := derivative_eq_accuracy hε.le h hk.le (j := 2) (by norm_num) (by omega)
      simp only [show (2 : ℕ) ≠ 3 by norm_num, ite_false] at hh
      rcases hs.2 with hs | hs
      · linarith
      · have hv := hs.2 1 (one_mem_directions_third hp hε.le h₂.le h)
        rw [directional_abs_eq_accuracy hε.le h hk.le (by norm_num) hp 1 (by norm_num)] at hv
        simp only [ite_true, ite_eq_left hk] at hv
        rw [he] at hv
        linarith [hv.1]
  · intro k hk
    exact stepConditions_of_matches hp hr hrp h hk (step_pos p r hε)

/-- The final actual first, second and third derivatives satisfy all source target tolerances. -/
theorem terminal_derivatives {f : ℝ → ℝ} {p r : ℕ}
    (hp : 3 ≤ p) (hr : 0 < r) (hr3 : r ≤ 3) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (h : MatchesJets f p r
      (length p r (selectedAccuracy r ε₁ ε₂ ε₃)) (amplitude p r)
      (step p r (selectedAccuracy r ε₁ ε₂ ε₃))) :
    let ε := selectedAccuracy r ε₁ ε₂ ε₃
    let x := iterate p r ε (length p r ε)
    ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ iteratedDeriv 2 f x ∧
      ∀ v : ℝ, ‖v‖ = 1 →
        |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂ ∧
        |iteratedFDeriv ℝ 3 f x (fun _ => v)| ≤ ε₃ := by
  generalize he : selectedAccuracy r ε₁ ε₂ ε₃ = ε at *
  have hε : 0 < ε := he ▸ selectedAccuracy_pos r h₁ h₂ h₃
  have hg := first_norm_eq_accuracy (by omega : 1 ≤ p) hε.le h le_rfl
  have hH := derivative_eq_accuracy hε.le h le_rfl (by norm_num : 0 < 2) (by omega)
  simp only [lt_self_iff_false, ite_false, one_mul, neg_one_mul] at hg hH
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    interval_cases r <;> simp_all [selectedAccuracy]
    all_goals linarith
  · rw [hH]
    interval_cases r <;> simp_all [selectedAccuracy]
    all_goals linarith
  · intro v hv
    have h₂v := directional_abs_eq_accuracy hε.le h le_rfl
      (by norm_num : 0 < 2) (by omega) v hv
    have h₃v := directional_abs_eq_accuracy hε.le h le_rfl
      (by norm_num : 0 < 3) hp v hv
    simp only [lt_self_iff_false, ite_false, one_mul] at h₂v h₃v
    rw [h₂v, h₃v]
    interval_cases r <;> simp_all only [selectedAccuracy, Nat.reduceEqDiff,
      OfNat.ofNat_ne_one, Nat.succ_ne_self, ite_true, ite_false]
    all_goals constructor <;> linarith

/-- The final inherited set is nonempty, so the literal nonempty stopping guard also holds. -/
theorem terminal_directions_nonempty (f : ℝ → ℝ) (p r : ℕ) {ε : ℝ}
    (hε : 0 < ε) (ε₂ : ℝ) :
    (directions f p r ε ε₂ (length p r ε)).Nonempty := by
  have hN := horizon_pos p (root_pos p r hε)
  have hn : length p r ε ≠ 0 := Nat.ne_of_gt hN
  simp only [directions, ite_eq_right hn]
  exact ⟨1, by norm_num⟩

/-- The final point passes the full third-order stopping test, including the literal guard. -/
theorem terminal_stop {f : ℝ → ℝ} {p r : ℕ}
    (hp : 3 ≤ p) (hr : 0 < r) (hr3 : r ≤ 3) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (h : MatchesJets f p r
      (length p r (selectedAccuracy r ε₁ ε₂ ε₃)) (amplitude p r)
      (step p r (selectedAccuracy r ε₁ ε₂ ε₃))) :
    let ε := selectedAccuracy r ε₁ ε₂ ε₃
    let x := iterate p r ε (length p r ε)
    finiteStop f x (iteratedDeriv 2 f x)
      (directions f p r ε ε₂ (length p r ε)) ε₁ ε₂ ε₃ ∧
      (directions f p r ε ε₂ (length p r ε)).Nonempty := by
  have hd := terminal_derivatives hp hr hr3 h₁ h₂ h₃ h
  refine ⟨⟨hd.1, Or.inr ⟨hd.2.1, ?_⟩⟩,
    terminal_directions_nonempty f p r (selectedAccuracy_pos r h₁ h₂ h₃) ε₂⟩
  intro v hv
  have hε := selectedAccuracy_pos r h₁ h₂ h₃
  have hN := horizon_pos p (root_pos p r hε)
  have hn : length p r (selectedAccuracy r ε₁ ε₂ ε₃) ≠ 0 := Nat.ne_of_gt hN
  rw [directions, ite_eq_right hn] at hv
  exact ⟨(hd.2.2 v hv).2, (hd.2.2 v hv).1⟩

/-- All trials are accepted, giving exactly `N+1` evaluations of each derivative order. -/
theorem derivativeEvaluations_one (N : ℕ) :
    HighOrderRegularization.derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1 := by
  norm_num [HighOrderRegularization.derivativeEvaluations,
    EvaluationComplexity.successfulIterations]

/-- Actual highest-order Fréchet regularity and objective bounds before accuracy is chosen. -/
theorem exists_uniform_objectives_actual {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ (∀ x, |f x| ≤ B) ∧
        (∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖) ∧
        MatchesJets f p r (length p r ε) (amplitude p r) (step p r ε) := by
  obtain ⟨L, hL, B, hB, hex⟩ := exists_uniform_objectives_accuracy hr hrp
  refine ⟨max 1 L, B, le_max_left _ _, hB, ?_⟩
  intro ε hε hε1
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hex ε hε hε1
  refine ⟨f, hf, fun x => ?_, ?_, hjet⟩
  · simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le _) x
  · intro x y
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
    exact (hLip.norm_sub_le x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- A common objective budget is available uniformly over every tested derivative order. -/
theorem exists_uniform_objectives_orders (p q : ℕ) (hqp : q ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ r : ℕ, 0 < r → r ≤ q → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ (∀ x, |f x| ≤ B) ∧
        (∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖) ∧
        MatchesJets f p r (length p r ε) (amplitude p r) (step p r ε) := by
  induction q with
  | zero =>
    refine ⟨1, 1, le_rfl, by norm_num, ?_⟩
    intro r hr hr0
    omega
  | succ q ih =>
    obtain ⟨L₀, B₀, hL₀, hB₀, h₀⟩ := ih (by omega)
    obtain ⟨L₁, B₁, hL₁, hB₁, h₁⟩ := exists_uniform_objectives_actual
      (by omega : 0 < q + 1) hqp
    refine ⟨max L₀ L₁, max B₀ B₁, hL₀.trans (le_max_left _ _),
      hB₀.trans_le (le_max_left _ _), ?_⟩
    intro r hr hrq ε hε hε1
    by_cases he : r = q + 1
    · subst r
      obtain ⟨f, hf, hb, hLip, hj⟩ := h₁ ε hε hε1
      exact ⟨f, hf, fun x => (hb x).trans (le_max_right _ _),
        fun x y => (hLip x y).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)), hj⟩
    · obtain ⟨f, hf, hb, hLip, hj⟩ := h₀ r hr (by omega) ε hε hε1
      exact ⟨f, hf, fun x => (hb x).trans (le_max_left _ _),
        fun x y => (hLip x y).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), hj⟩

/-- The terminal first-order derivative attains the requested accuracy exactly. -/
theorem terminal_first_order {f : ℝ → ℝ} {p : ℕ} (hp : 1 ≤ p) {ε : ℝ}
    (hε : 0 ≤ ε)
    (h : MatchesJets f p 1 (length p 1 ε) (amplitude p 1) (step p 1 ε)) :
    ‖fderiv ℝ f (iterate p 1 ε (length p 1 ε))‖ = ε := by
  simpa only [ite_true, lt_self_iff_false, ite_false, one_mul] using
    first_norm_eq_accuracy hp hε h le_rfl

/-- The terminal first and second derivatives satisfy the finite-second-order target. -/
theorem terminal_second_order {f : ℝ → ℝ} {p r : ℕ}
    (hp : 2 ≤ p) (hr : 0 < r) (hr2 : r ≤ 2) {ε₁ ε₂ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂)
    (h : MatchesJets f p r
      (length p r (selectedAccuracy r ε₁ ε₂ 1)) (amplitude p r)
      (step p r (selectedAccuracy r ε₁ ε₂ 1))) :
    let ε := selectedAccuracy r ε₁ ε₂ 1
    let x := iterate p r ε (length p r ε)
    ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ iteratedDeriv 2 f x := by
  generalize he : selectedAccuracy r ε₁ ε₂ 1 = ε at *
  have hε : 0 < ε := he ▸ selectedAccuracy_pos r h₁ h₂ (by norm_num)
  have hg := first_norm_eq_accuracy (by omega : 1 ≤ p) hε.le h le_rfl
  have hH := derivative_eq_accuracy hε.le h le_rfl (by norm_num : 0 < 2) hp
  simp only [lt_self_iff_false, ite_false, one_mul, neg_one_mul] at hg hH
  refine ⟨?_, ?_⟩
  · rw [hg]
    interval_cases r <;> simp_all [selectedAccuracy]
    all_goals linarith
  · rw [hH]
    interval_cases r <;> simp_all [selectedAccuracy]
    all_goals linarith

/-- Passing the literal source guard always passes the weaker repaired test. -/
theorem literalStop_imp_finiteStop {f : ℝ → ℝ} {x ε₁ ε₂ ε₃ : ℝ} {M : Set ℝ}
    (h : HighOrderRegularization.EmptyDirections.literalStop f x M ε₁ ε₂ ε₃) :
    finiteStop f x (iteratedDeriv 2 f x) M ε₁ ε₂ ε₃ := by
  refine ⟨by simpa only [norm_deriv_eq_norm_fderiv] using h.1, ?_⟩
  rcases h.2 with hh | hh
  · exact Or.inl hh
  · exact Or.inr ⟨hh.1, hh.2.2⟩

/-- A nonempty inherited direction set restores the literal source stopping guard. -/
theorem literalStop_of_finiteStop_of_nonempty {f : ℝ → ℝ}
    {x ε₁ ε₂ ε₃ : ℝ} {M : Set ℝ}
    (h : finiteStop f x (iteratedDeriv 2 f x) M ε₁ ε₂ ε₃) (hM : M.Nonempty) :
    HighOrderRegularization.EmptyDirections.literalStop f x M ε₁ ε₂ ε₃ := by
  refine ⟨by simpa only [norm_deriv_eq_norm_fderiv] using h.1, ?_⟩
  rcases h.2 with hh | hh
  · exact Or.inl hh
  · exact Or.inr ⟨hh.1, hM, hh.2⟩

end HighOrderRegularization.Sharpness
