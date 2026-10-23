import Numlib.Optimization.TrustRegion.SecondOrder.FirstOrder
import Numlib.Optimization.TrustRegion.Eigenpoint

/-!
# Finite-second-order trust-region traces and radius bounds

Both stopping tests use actual derivatives. Least eigenpairs are certified by
an eigenvector equation and the Rayleigh lower bound on every unit direction.
The trace contains only the algorithm's step, ratio and update rules.
-/

namespace SecondOrderTrustRegion
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A unit eigenvector for the least actual Hessian eigenvalue. -/
structure IsLeastEigenpair (f : E → ℝ) (x : E) (μ : ℝ) (u : E) : Prop where
  unit : ‖u‖ = 1
  eigenvector : TaylorModel.hessianOperator f x u = μ • u
  least : ∀ v : E, ‖v‖ = 1 → μ ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)

/-- Complete TR2 rules with both finite stopping tolerances. -/
structure Run (f : E → ℝ) (x s sC sE u : ℕ → E) (μ Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ : ℝ) (N : ℕ) : Prop where
  updates : EvaluationComplexity.TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N
  accuracy_first_pos : 0 < ε₁
  accuracy_second_pos : 0 < ε₂
  least_eigenpair : ∀ i ≤ N, IsLeastEigenpair f (x i) (μ i) (u i)
  eigenvector_sign : ∀ i < N, inner ℝ (gradient f (x i)) (u i) ≤ 0
  not_terminated : ∀ i < N, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂
  cauchy : ∀ i < N, IsCauchyPoint f (x i) (Δ i) (sC i)
  eigenpoint : ∀ i < N, if μ i < 0 then
    TaylorModel.IsEigenPoint f (x i) (u i) (Δ i) (sE i) else sE i = 0
  feasible_step : ∀ i < N, ‖s i‖ ≤ Δ i
  model_cauchy : ∀ i < N,
    TaylorModel.eval f 2 (x i) (s i) ≤ TaylorModel.eval f 2 (x i) (sC i)
  model_eigen : ∀ i < N,
    TaylorModel.eval f 2 (x i) (s i) ≤ TaylorModel.eval f 2 (x i) (sE i)
  ratio : ∀ i < N, ρ i = (f (x i) - f (x i + s i)) /
    (TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) (s i))
  step : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

/-- The two model-improvement requirements admit a feasible common trial step. -/
theorem exists_modelStep (f : E → ℝ) (x u : E) {μ Δ : ℝ}
    (hu : ‖u‖ = 1) (hΔ : 0 ≤ Δ) :
    ∃ sC sE s : E, IsCauchyPoint f x Δ sC ∧
      (if μ < 0 then TaylorModel.IsEigenPoint f x u Δ sE else sE = 0) ∧
      ‖s‖ ≤ Δ ∧ TaylorModel.eval f 2 x s ≤ TaylorModel.eval f 2 x sC ∧
      TaylorModel.eval f 2 x s ≤ TaylorModel.eval f 2 x sE := by
  obtain ⟨sC, hc⟩ := exists_cauchyPoint f x hΔ
  have hcn : ‖sC‖ ≤ Δ := by
    rcases hc with ⟨t, _, ht, he, _⟩
    simpa [he] using ht
  have hex : ∃ sE : E,
      (if μ < 0 then TaylorModel.IsEigenPoint f x u Δ sE else sE = 0) ∧ ‖sE‖ ≤ Δ := by
    by_cases hm : μ < 0
    · obtain ⟨sE, hp⟩ := TaylorModel.exists_eigenPoint f x u hΔ
      refine ⟨sE, by simpa only [ite_eq_left hm] using hp, ?_⟩
      rcases hp with ⟨t, ht, rfl, _⟩
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hu] using ht.2
    · exact ⟨0, by simp [hm], by simpa using hΔ⟩
  obtain ⟨sE, he, hen⟩ := hex
  by_cases hcmp : TaylorModel.eval f 2 x sC ≤ TaylorModel.eval f 2 x sE
  · exact ⟨sC, sE, sC, hc, he, hcn, le_rfl, hcmp⟩
  · exact ⟨sC, sE, sE, hc, he, hen, (le_of_not_ge hcmp), le_rfl⟩

/-- The source's accuracy-independent radius constant. -/
noncomputable def secondOrderRadiusConstant (Δ₀ η₂ γ₁ H L : ℝ) : ℝ :=
  min (γ₁ * (1 - η₂) / max (4 * H) (L / 3)) Δ₀

namespace Run
variable {f : E → ℝ} {x s sC sE u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ H L : ℝ} {N : ℕ}

/-- A gradient-nonterminal trial is a genuine one-trial first-order TR2 run. -/
theorem firstOrderTrial (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) (hg : ε₁ < ‖gradient f (x i)‖) :
    FirstOrderRun f (fun j => x (i + j)) (fun j => s (i + j))
      (fun j => sC (i + j)) (fun j => Δ (i + j)) (fun j => ρ (i + j))
      η₁ η₂ γ₁ γ₂ γ₃ ε₁ ⊤ 1 where
  second_order_disabled := rfl
  updates := {
    initial_pos := by simpa using h.updates.pos (show i ≤ N by omega)
    eta1_pos := h.updates.eta1_pos
    eta1_le_eta2 := h.updates.eta1_le_eta2
    eta2_lt_one := h.updates.eta2_lt_one
    gamma1_pos := h.updates.gamma1_pos
    gamma1_le_gamma2 := h.updates.gamma1_le_gamma2
    gamma2_lt_one := h.updates.gamma2_lt_one
    one_lt_gamma3 := h.updates.one_lt_gamma3
    update := by
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa using h.updates.update i hi }
  accuracy_pos := h.accuracy_first_pos
  not_terminated := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using hg
  cauchy := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using h.cauchy i hi
  feasible_step := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using h.feasible_step i hi
  model_step := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using h.model_cauchy i hi
  ratio := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using h.ratio i hi
  step := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using h.step i hi

/-- Every nonterminal trial has a strictly positive actual predicted decrease. -/
theorem denominator_pos (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i < N) :
    0 < TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) (s i) := by
  rcases h.not_terminated i hi with hg | hc
  · have hh := ((h.firstOrderTrial hi hg).to_firstOrder hf).denominator_pos
      (i := 0) (by norm_num)
    simpa only [Nat.add_zero, model_eq_taylor] using hh
  · have hc0 : μ i < 0 := by linarith [h.accuracy_second_pos]
    have hp := h.eigenpoint i hi
    rw [ite_eq_left hc0] at hp
    exact TaylorModel.eigenpoint_predicted_decrease_pos f (x i) (u i)
      (h.updates.pos (show i ≤ N by omega)) hc0 (h.least_eigenpair i (by omega)).unit
      (h.least_eigenpair i (by omega)).eigenvector (h.eigenvector_sign i hi) hp
      (h.model_eigen i hi)

/-- A sufficiently small radius is very successful in either nontermination branch. -/
theorem very_successful (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N)
    (hsmall : Δ i < (1 - η₂) * min ε₁ ε₂ / max (4 * H) (L / 3)) : η₂ ≤ ρ i := by
  have hHp : 0 < H := by linarith
  have hη : 0 < 1 - η₂ := by linarith [h.updates.eta2_lt_one]
  have hm : 0 < min ε₁ ε₂ := lt_min h.accuracy_first_pos h.accuracy_second_pos
  rcases h.not_terminated i hi with hg | hc
  · have hs₁ : Δ i < (1 - η₂) * ‖gradient f (x i)‖ / (4 * H) := by
      apply hsmall.trans_le
      calc
        _ ≤ (1 - η₂) * min ε₁ ε₂ / (4 * H) :=
          div_le_div_of_nonneg_left (mul_nonneg hη.le hm.le) (by positivity)
            (le_max_left _ _)
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((min_le_left ε₁ ε₂).trans hg.le) hη.le) (by positivity)
    have hr := (h.firstOrderTrial hi hg).to_firstOrder hf
    have hh := hr.very_successful (gradient_lipschitz_of_hessian_bound hf hHp.le hbound)
      hH (fun j _ => hbound (x (i + j))) (i := 0) (by norm_num)
      (by simpa only [Nat.add_zero, show (2 : ℝ) * (H + H) = 4 * H by ring] using hs₁)
    simpa using hh
  · have hc0 : μ i < 0 := by linarith [h.accuracy_second_pos]
    have hs₂ : Δ i < 3 * (1 - η₂) * |μ i| / L := by
      apply hsmall.trans_le
      calc
        _ ≤ (1 - η₂) * min ε₁ ε₂ / (L / 3) :=
          div_le_div_of_nonneg_left (mul_nonneg hη.le hm.le) (by positivity)
            (le_max_right _ _)
        _ ≤ (1 - η₂) * |μ i| / (L / 3) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hη.le
          rw [abs_of_neg hc0]
          linarith [min_le_right ε₁ ε₂]
        _ = _ := by ring
    have hp := h.eigenpoint i hi
    rw [ite_eq_left hc0] at hp
    exact TaylorModel.eigen_trial_very_successful f (x i) (u i) hf hL hlip
      (h.updates.pos (show i ≤ N by omega)) hc0 (h.least_eigenpair i (by omega)).unit
      (h.least_eigenpair i (by omega)).eigenvector (h.eigenvector_sign i hi) hp
      (h.model_eigen i hi) (h.feasible_step i hi) h.updates.eta2_lt_one hs₂ (h.ratio i hi)

/-- The exact radius coefficient is strictly between zero and one. -/
theorem radiusConstant_mem_Ioo (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hH : 1 ≤ H) (_hL : 0 ≤ L) :
    secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L ∈ Ioo 0 1 := by
  have hHp : 0 < H := by linarith
  have hd : 0 < max (4 * H) (L / 3) := (by positivity : 0 < 4 * H).trans_le (le_max_left _ _)
  have hηpos : 0 < η₂ := h.updates.eta1_pos.trans_le h.updates.eta1_le_eta2
  have hγ : γ₁ < 1 := h.updates.gamma1_le_gamma2.trans_lt h.updates.gamma2_lt_one
  unfold secondOrderRadiusConstant
  constructor
  · exact lt_min (div_pos (mul_pos h.updates.gamma1_pos (by linarith [h.updates.eta2_lt_one])) hd)
      h.updates.initial_pos
  · apply (min_le_left _ _).trans_lt
    apply (div_lt_one hd).mpr
    have hprod : γ₁ * (1 - η₂) < 1 := by nlinarith [h.updates.gamma1_pos]
    linarith [le_max_left (4 * H) (L / 3)]

/-- Both finite stopping tests yield the uniform second-order radius lower bound. -/
theorem radius_lower (h : Run f x s sC sE u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hH : 1 ≤ H) (hL : 0 < L) (hε₂ : ε₂ ≤ 1)
    (hbound : ∀ y, ‖hessian f y‖ ≤ H)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) :
    secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L * min ε₁ ε₂ ≤ Δ i := by
  have hb := h.updates.min_initial_threshold_le
    (fun j hj hs => h.very_successful hf hH hL hbound hlip hj hs) hi
  apply le_trans _ hb
  apply le_min
  · have hm : min ε₁ ε₂ ≤ 1 := (min_le_right ε₁ ε₂).trans hε₂
    have hk := (h.radiusConstant_mem_Ioo hH hL.le).1
    calc
      _ ≤ secondOrderRadiusConstant (Δ 0) η₂ γ₁ H L := by nlinarith
      _ ≤ Δ 0 := min_le_right _ _
  · unfold secondOrderRadiusConstant
    have hm : 0 ≤ min ε₁ ε₂ := le_min h.accuracy_first_pos.le h.accuracy_second_pos.le
    calc
      _ ≤ (γ₁ * (1 - η₂) / max (4 * H) (L / 3)) * min ε₁ ε₂ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hm
      _ = _ := by ring
end Run
end SecondOrderTrustRegion
