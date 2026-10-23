import Numlib.Optimization.Regularization.InexactNewton.Run

/-!
# Acceptance and upper-parameter bounds for inexact regularized Newton steps

The actual model slope bound and sharp Taylor value remainder imply acceptance
for a sufficiently large multiplier. The coupled upper/lower update mechanism
then bounds the upper parameter uniformly; this bound is not a run invariant.
-/

namespace InexactRegularizedNewton
open TaylorModel Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The slope condition on the actual quadratic model gives the Taylor
value reduction, before accounting for the true objective remainder. -/
theorem Step.taylor_decrease {f : E → ℝ} {x s : E} {ℓ σL σU κ₁ κ₂ κ₃ : ℝ}
    (h : Step f x s ℓ σL σU κ₁ κ₂ κ₃) (hf : ContDiffAt ℝ 2 f x) :
    ℓ / 2 * ‖s‖ ^ 2 - κ₂ / 2 * ‖s‖ ^ 3 ≤ eval f 2 x 0 - eval f 2 x s := by
  have hs := h.slope.trans (min_le_right _ _)
  rw [RegularizedTrustRegion.fderiv_model hf,
    RegularizedTrustRegion.iteratedFDeriv_two_model_diag hf] at hs
  simp only [iteratedFDeriv_two_apply, quadraticDerivative, add_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq] at hs
  rw [eval_zero, eval_two_eq]
  linarith

/-- The source upper-parameter cap is independent of all stopping accuracies. -/
noncomputable def upperBound (σmax γ₂ η κ₂ L : ℝ) : ℝ :=
  max σmax (γ₂ * (2 * η + κ₂ + L))

namespace Run
variable {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
  {μ ℓ σL σU ρ : ℕ → ℝ}
  {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L : ℝ}
  {ε₂ : WithTop ℝ} {N : ℕ}

/-- A multiplier above the explicit threshold guarantees actual cubic descent
and acceptance, using a positive denominator derived from nontermination. -/
theorem successful_of_large_multiplier
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N)
    (hlarge : (2 * η + κ₂ + L) * ‖s i‖ ≤ ℓ i) : η ≤ ρ i := by
  have hs := h.step_ne_zero hf hi
  have hn : 0 < ‖s i‖ := norm_pos_iff.mpr hs
  have hd := (h.step i hi.le (Or.inl hi)).taylor_decrease hf.contDiffAt
  have herr := abs_sub_eval_le_lipschitz (p := 1) (C := univ) (D := univ)
    isOpen_univ (Subset.refl _) convex_univ hf.contDiffOn hL
    (fun y _ z _ => hlip y z) (mem_univ (x i)) (mem_univ (x i + s i))
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at herr
  have he := (abs_le.mp herr).2
  have hm := mul_le_mul_of_nonneg_right hlarge (sq_nonneg ‖s i‖)
  have hnonneg := mul_nonneg hL (pow_nonneg hn.le 3)
  rw [h.ratio i hi]
  apply (le_div_iff₀ (pow_pos hn 3)).mpr
  rw [eval_zero] at hd
  nlinarith

/-- The actual three-branch coupled updates imply the source's uniform upper
parameter bound at all endpoints, including the terminal one. -/
theorem upper_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) : σU i ≤ upperBound σmax γ₂ η κ₂ L := by
  have hγ : 0 < γ₂ := zero_lt_one.trans (h.gamma1_gt_one.trans_le h.gamma1_le_gamma2)
  induction i with
  | zero => exact h.upper_initial.2.trans (le_max_left _ _)
  | succ i ih =>
    have hb := h.update i (by omega)
    split_ifs at hb with ha hsmall
    · rw [hb.2]
      exact ih (by omega)
    · exact hb.2.2.trans (le_max_left _ _)
    · rw [hb.2]
      have hfail : ℓ i < (2 * η + κ₂ + L) * ‖s i‖ :=
        lt_of_not_ge (fun hh => ha (h.successful_of_large_multiplier hf hL hlip (by omega) hh))
      have hn : 0 < ‖s i‖ := norm_pos_iff.mpr (h.step_ne_zero hf (by omega))
      have hratio : ℓ i / ‖s i‖ ≤ 2 * η + κ₂ + L := (div_le_iff₀ hn).mpr hfail.le
      exact (mul_le_mul_of_nonneg_left hratio hγ.le).trans (le_max_right _ _)

/-- The uniform upper parameter gives the corresponding actual multiplier bound. -/
theorem multiplier_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) (hcomputed : i < N ∨ ε₂ ≠ ⊤) :
    ℓ i ≤ upperBound σmax γ₂ η κ₂ L * ‖s i‖ :=
  (h.step i hi hcomputed).upper.trans
    (mul_le_mul_of_nonneg_right (h.upper_le hf hL hlip hi) (norm_nonneg _))

/-- The uniform cap is positive because it dominates the positive initialized
regularization range, independently of stopping tolerances. -/
theorem upperBound_pos
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) :
    0 < upperBound σmax γ₂ η κ₂ L :=
  (h.sigmaMin_pos.trans_le h.sigmaMin_le_max).trans_le (le_max_left _ _)

end Run
end InexactRegularizedNewton
