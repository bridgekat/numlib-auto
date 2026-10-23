import Numlib.Optimization.Regularization.HighOrder.Sharpness.Execution

/-!
# Sharp first- to third-order regularization examples

One derivative order attains the maximum of the requested inverse-accuracy rates.
Uniform Hermite objectives realize that slow branch with a fixed legal parameter,
unit model-test tolerances, actual unit acceptance ratios and exact evaluation
counters. First and second branches explicitly disable the unused tests. The
third branch satisfies the literal nonempty-direction stopping guard as well.
-/

namespace HighOrderRegularization.Sharpness

/-- The source inverse-accuracy evaluation rate for a selected derivative order. -/
noncomputable def rate (p r : ℕ) (ε : ℝ) : ℝ :=
  ε ^ (-((p + 1 : ℕ) : ℝ) / balance p r)

/-- At first order the balancing exponent is the source exponent `(p+1)/p`. -/
theorem rate_one {p : ℕ} (hp : 1 ≤ p) (ε : ℝ) :
    rate p 1 ε = ε ^ (-((p + 1 : ℕ) : ℝ) / p) := by
  rw [rate, balance, Nat.sub_add_cancel hp]

/-- At second order the balancing exponent is the source exponent `(p+1)/(p-1)`. -/
theorem rate_two {p : ℕ} (hp : 2 ≤ p) (ε : ℝ) :
    rate p 2 ε = ε ^ (-((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) := by
  rw [rate, balance, show p - 2 + 1 = p - 1 by omega]

/-- At third order the balancing exponent is the source exponent `(p+1)/(p-2)`. -/
theorem rate_three {p : ℕ} (hp : 3 ≤ p) (ε : ℝ) :
    rate p 3 ε = ε ^ (-((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) := by
  rw [rate, balance, show p - 3 + 1 = p - 2 by omega]

/-- The actual trial count is exactly the ceiling of its selected source rate. -/
theorem length_eq_ceil_rate (p r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    length p r ε = ⌈rate p r ε⌉₊ := by
  rw [length, horizon, inverse_root_power hε, rate]

/-- A first or second derivative order attains the maximum of the two source rates. -/
theorem exists_maximizing_order_two (p : ℕ) (ε₁ ε₂ : ℝ) :
    ∃ r : ℕ, 0 < r ∧ r ≤ 2 ∧
      max (rate p 1 ε₁) (rate p 2 ε₂) = rate p r (selectedAccuracy r ε₁ ε₂ 1) := by
  by_cases hh : rate p 1 ε₁ ≤ rate p 2 ε₂
  · exact ⟨2, by omega, le_rfl, by simpa [selectedAccuracy] using max_eq_right hh⟩
  · exact ⟨1, by omega, by omega,
      by simpa [selectedAccuracy] using max_eq_left (le_of_not_ge hh)⟩

/-- One of the first three derivative orders attains the maximum source rate. -/
theorem exists_maximizing_order_three (p : ℕ) (ε₁ ε₂ ε₃ : ℝ) :
    ∃ r : ℕ, 0 < r ∧ r ≤ 3 ∧
      max (max (rate p 1 ε₁) (rate p 2 ε₂)) (rate p 3 ε₃) =
        rate p r (selectedAccuracy r ε₁ ε₂ ε₃) := by
  by_cases hh : max (rate p 1 ε₁) (rate p 2 ε₂) ≤ rate p 3 ε₃
  · exact ⟨3, by omega, le_rfl, by simpa [selectedAccuracy] using max_eq_right hh⟩
  · obtain ⟨r, hr, hr2, he⟩ := exists_maximizing_order_two p ε₁ ε₂
    refine ⟨r, hr, by omega, ?_⟩
    rw [max_eq_left (le_of_not_ge hh), he]
    interval_cases r <;> simp [selectedAccuracy]

/-- Full first-order sharpness: objective constants precede accuracy, actual run
and stopping hold, and both actual evaluation counters exceed the source rate. -/
theorem exists_first_order_witness {p : ℕ} (hp : 1 ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ,
        let N := length p 1 ε
        let x := iterate p 1 ε
        ContDiff ℝ p f ∧ (∀ z, |f z| ≤ B) ∧
        (∀ z w, ‖iteratedFDeriv ℝ p f z - iteratedFDeriv ℝ p f w‖ ≤ L * ‖z - w‖) ∧
        FirstOrderRun f p x (fun _ => step p 1 ε)
          (fun _ => parameter p) (fun _ => 1)
          (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 ε ⊤ ⊤ N ∧
        ‖fderiv ℝ f (x N)‖ = ε ∧
        rate p 1 ε ≤ (N : ℝ) ∧
        functionEvaluations N = N + 1 ∧
        derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1 := by
  obtain ⟨L, B, hL, hB, hex⟩ := exists_uniform_objectives_actual (by norm_num) hp
  refine ⟨L, B, hL, hB, ?_⟩
  intro ε hε hε1
  obtain ⟨f, hf, hb, hLip, hj⟩ := hex ε hε hε1
  exact ⟨f, hf, hb, hLip, firstOrderRun_of_matches hp hε hε1 hj,
    terminal_first_order hp hε.le hj, inverse_accuracy_le_horizon hε,
    rfl, derivativeEvaluations_one _⟩

/-- Full second-order sharpness with one common fixed parameter and uniform
objective constants before both accuracies. A genuine slow branch attains the maximum rate. -/
theorem exists_second_order_witness {p : ℕ} (hp : 2 ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
      ∃ r : ℕ, 0 < r ∧ r ≤ 2 ∧ ∃ f : ℝ → ℝ,
        let ε := selectedAccuracy r ε₁ ε₂ 1
        let N := length p r ε
        let x := iterate p r ε
        ContDiff ℝ p f ∧ (∀ z, |f z| ≤ B) ∧
        (∀ z w, ‖iteratedFDeriv ℝ p f z - iteratedFDeriv ℝ p f w‖ ≤ L * ‖z - w‖) ∧
        SecondOrderRun f p x (fun _ => step p r ε) (fun _ => 1)
          (fun k => iteratedDeriv 2 f (x k)) (fun _ => parameter p) (fun _ => 1)
          (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 1 ε₁ ε₂ ⊤ N ∧
        ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ iteratedDeriv 2 f (x N) ∧
        max (rate p 1 ε₁) (rate p 2 ε₂) ≤ (N : ℝ) ∧
        functionEvaluations N = N + 1 ∧
        derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1 := by
  obtain ⟨L, B, hL, hB, hex⟩ := exists_uniform_objectives_orders p 2 hp
  refine ⟨L, B, hL, hB, ?_⟩
  intro ε₁ ε₂ h₁ h₁1 h₂ h₂1
  obtain ⟨r, hr, hr2, he⟩ := exists_maximizing_order_two p ε₁ ε₂
  have hε : 0 < selectedAccuracy r ε₁ ε₂ 1 :=
    selectedAccuracy_pos r h₁ h₂ (by norm_num)
  have hε1 : selectedAccuracy r ε₁ ε₂ 1 ≤ 1 :=
    selectedAccuracy_le_one r h₁1 h₂1 (by norm_num)
  obtain ⟨f, hf, hb, hLip, hj⟩ := hex r hr hr2 _ hε hε1
  have hstop := terminal_second_order hp hr hr2 h₁ h₂ hj
  refine ⟨r, hr, hr2, f, hf, hb, hLip,
    secondOrderRun_of_matches hp hr hr2 h₁ h₁1 h₂ h₂1 hj,
    hstop.1, hstop.2, ?_, rfl, derivativeEvaluations_one _⟩
  rw [he]
  exact inverse_accuracy_le_horizon hε

/-- Full third-order sharpness with actual all-direction terminal derivatives,
nonempty inherited model directions and the maximum of all three source rates. -/
theorem exists_third_order_witness {p : ℕ} (hp : 3 ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ ε₁ ε₂ ε₃ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
        0 < ε₃ → ε₃ ≤ 1 →
      ∃ r : ℕ, 0 < r ∧ r ≤ 3 ∧ ∃ f : ℝ → ℝ,
        let ε := selectedAccuracy r ε₁ ε₂ ε₃
        let N := length p r ε
        let x := iterate p r ε
        let M := directions f p r ε ε₂
        ContDiff ℝ p f ∧ (∀ z, |f z| ≤ B) ∧
        (∀ z w, ‖iteratedFDeriv ℝ p f z - iteratedFDeriv ℝ p f w‖ ≤ L * ‖z - w‖) ∧
        FiniteRun f p x (fun _ => step p r ε) (fun _ => 1)
          (fun k => iteratedDeriv 2 f (x k)) (fun _ => parameter p) (fun _ => 1) M
          (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 1 1 ε₁ ε₂ ε₃ N ∧
        finiteStop f (x N) (iteratedDeriv 2 f (x N)) (M N) ε₁ ε₂ ε₃ ∧ (M N).Nonempty ∧
        HighOrderRegularization.EmptyDirections.literalStop f (x N) (M N) ε₁ ε₂ ε₃ ∧
        (∀ k < N, ¬HighOrderRegularization.EmptyDirections.literalStop
          f (x k) (M k) ε₁ ε₂ ε₃) ∧
        ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ iteratedDeriv 2 f (x N) ∧
        (∀ v : ℝ, ‖v‖ = 1 →
          |iteratedFDeriv ℝ 2 f (x N) (fun _ => v)| ≤ ε₂ ∧
          |iteratedFDeriv ℝ 3 f (x N) (fun _ => v)| ≤ ε₃) ∧
        max (max (rate p 1 ε₁) (rate p 2 ε₂)) (rate p 3 ε₃) ≤ (N : ℝ) ∧
        functionEvaluations N = N + 1 ∧
        derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1 := by
  obtain ⟨L, B, hL, hB, hex⟩ := exists_uniform_objectives_orders p 3 hp
  refine ⟨L, B, hL, hB, ?_⟩
  intro ε₁ ε₂ ε₃ h₁ h₁1 h₂ h₂1 h₃ h₃1
  obtain ⟨r, hr, hr3, he⟩ := exists_maximizing_order_three p ε₁ ε₂ ε₃
  have hε := selectedAccuracy_pos r h₁ h₂ h₃
  have hε1 := selectedAccuracy_le_one r h₁1 h₂1 h₃1
  obtain ⟨f, hf, hb, hLip, hj⟩ := hex r hr hr3 _ hε hε1
  have hstop := terminal_stop hp hr hr3 h₁ h₂ h₃ hj
  have hd := terminal_derivatives hp hr hr3 h₁ h₂ h₃ hj
  have hRun := finiteRun_of_matches hp hr hr3 h₁ h₁1 h₂ h₂1 h₃ h₃1 hj
  refine ⟨r, hr, hr3, f, hf, hb, hLip, hRun,
    hstop.1, hstop.2, literalStop_of_finiteStop_of_nonempty hstop.1 hstop.2,
    ?_, hd.1, hd.2.1, hd.2.2, ?_, rfl, derivativeEvaluations_one _⟩
  · intro k hk hs
    exact hRun.not_terminated k hk (literalStop_imp_finiteStop hs)
  · rw [he]
    exact inverse_accuracy_le_horizon hε

end HighOrderRegularization.Sharpness
