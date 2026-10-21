import Numlib.Optimization.FlatJetChain
import Numlib.Analysis.Calculus.EuclideanOne
import Numlib.Optimization.FirstOrderRegularization

/-!
# Uniform hard chains for first-order methods

Globally smooth bounded objectives realize a chain of exact negative-gradient unit steps.
The Lipschitz and objective-gap constants are fixed before the accuracy tolerance is chosen.
-/
noncomputable section
namespace Optimization.LowerBound
open scoped NNReal
open EuclideanOne

/-- Uniform hard chains with a stationary endpoint and exact linear-model reductions. -/
theorem exists_firstOrder_chain :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x : ℕ → EuclideanSpace ℝ (Fin 1)),
        ContDiff ℝ 1 f ∧
        (∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖) ∧
        (∀ u, -B ≤ f u) ∧ f (x 0) = 0 ∧
        ε⁻¹ ^ 2 ≤ (N : ℝ) ∧
        (∀ k < N, ‖gradient f (x k)‖ = 2 * ε) ∧ gradient f (x N) = 0 ∧
        (∀ k, x (k + 1) = x k - gradient f (x k)) ∧
        (∀ k, f (x k) - f (x (k + 1)) = ‖gradient f (x k)‖ ^ 2) := by
  obtain ⟨L, B, hchain⟩ := exists_flatJet_chain 1 (by omega) 8 (by norm_num)
  refine ⟨max 1 (L : ℝ), B, le_max_left _ _, B.coe_nonneg, ?_⟩
  intro ε he he1
  let N : ℕ := ⌈ε⁻¹ ^ 2⌉₊
  have hNlower : ε⁻¹ ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNpos : 0 < N := by
    have : 0 < (N : ℝ) := (sq_pos_of_pos (inv_pos.mpr he)).trans_le hNlower
    exact_mod_cast this
  have hNupper : (N : ℝ) < ε⁻¹ ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg _)
  have he2 : ε ^ 2 ≤ 1 := by nlinarith
  have hcancel : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by field_simp
  have hdrop : (N : ℝ) * (2 * ε) * (2 * ε) ≤ 8 := by
    have := mul_le_mul_of_nonneg_right hNupper.le (sq_nonneg ε)
    nlinarith
  obtain ⟨f, hf, hLip, hj, hb⟩ := hchain N hNpos (2 * ε) (2 * ε) (by positivity)
    (by positivity) (by nlinarith) hdrop (by linarith) (by linarith)
  let x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => coord.symm ((min k N : ℕ) * (2 * ε))
  have hfx (k : ℕ) : lift f (x k) = -(min k N : ℕ) * (2 * ε) * (2 * ε) := by
    have hh := hj (min k N) (Nat.min_le_right _ _) 0 (by omega)
    simpa [lift, x, flatJet] using hh
  have hgx (k : ℕ) : gradient (lift f) (x k) =
      if k < N then coord.symm (-(2 * ε)) else 0 := by
    rw [gradient_eq_deriv hf.differentiable_one]
    have hh := hj (min k N) (Nat.min_le_right _ _) 1 (by omega)
    simp only [iteratedDeriv_one] at hh
    simp only [x, coord.apply_symm_apply]
    rw [hh]
    by_cases hk : k < N
    · simp [flatJet, Nat.min_eq_left hk.le, hk]
    · simp [flatJet, Nat.min_eq_right (by omega : N ≤ k), hk]
  have hstep (k : ℕ) : x (k + 1) = x k - gradient (lift f) (x k) := by
    rw [hgx]
    by_cases hk : k < N
    · simp only [hk, ↓reduceIte, x]
      apply coord.injective
      simp only [map_sub, coord.apply_symm_apply]
      rw [Nat.min_eq_left (by omega : k + 1 ≤ N), Nat.min_eq_left hk.le]
      push_cast
      ring
    · simp only [hk, ↓reduceIte, sub_zero]
      dsimp only [x]
      rw [Nat.min_eq_right (by omega : N ≤ k), Nat.min_eq_right (by omega : N ≤ k + 1)]
  refine ⟨lift f, N, x, contDiff hf, ?_, ?_, ?_, hNlower, ?_, ?_, hstep, ?_⟩
  · intro u v
    have h := (gradient_lipschitz hf.differentiable_one (by simpa using hLip)).norm_sub_le u v
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · intro u
    exact (abs_le.mp (by simpa using hb 0 (by omega) (coord u))).1
  · rw [hfx]
    simp
  · intro k hk
    rw [hgx, ite_eq_left hk, coord.symm.norm_map, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  · simp [hgx]
  · intro k
    rw [hfx, hfx, hgx]
    by_cases hk : k < N
    · simp only [hk, ↓reduceIte, coord.symm.norm_map, Real.norm_eq_abs,
        abs_neg, abs_of_pos (by positivity : 0 < 2 * ε)]
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left (by omega : k + 1 ≤ N)]
      push_cast
      ring
    · simp [hk, Nat.min_eq_right (by omega : N ≤ k), Nat.min_eq_right (by omega : N ≤ k+1)]

/-- Exact unit negative-gradient steps with exact linear decrease are legal first-trial
Armijo steps for every sufficient-decrease fraction below one. -/
theorem unitSteps_isBacktrackingSequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : E → ℝ} {g : E → E} {x : ℕ → E}
    (hstep : ∀ k, x (k + 1) = x k - g (x k))
    (hdrop : ∀ k, f (x k) - f (x (k + 1)) = ‖g (x k)‖ ^ 2)
    {α ε : ℝ} (ha : α ≤ 1) :
    SmoothDescent.IsBacktrackingSequence f g α 1 ε x (fun _ => 0) := by
  constructor
  · intro k _
    refine ⟨?_, by omega⟩
    simp only [SmoothDescent.backtrackingStep_zero, LineSearch.Armijo, one_smul,
      map_neg, innerSL_apply_apply, real_inner_self_eq_norm_sq, mul_neg]
    rw [← sub_eq_add_neg, ← hstep k]
    have := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖g (x k)‖)
    linarith [hdrop k]
  · intro k _
    simpa only [SmoothDescent.backtrackingStep_zero, one_smul] using hstep k

/-- Every ratio on an exact linear-decrease unit-step chain equals one, including the
stationary continuation. -/
theorem unitSteps_ratio_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x : ℕ → E}
    (hstep : ∀ k, x (k + 1) = x k - g (x k))
    (hdrop : ∀ k, f (x k) - f (x (k + 1)) = ‖g (x k)‖ ^ 2) (k : ℕ) :
    FirstOrderRegularization.ratio f g (x k) 1 = 1 := by
  classical
  unfold FirstOrderRegularization.ratio FirstOrderRegularization.trial
  split_ifs with hg
  · rfl
  · simp only [inv_one, one_smul, ← hstep k, hdrop, div_one]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hg))

/-- Constant unit regularization is a legal AR1 choice on an exact linear-decrease chain. -/
theorem unitSteps_isRegularizationRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x : ℕ → E}
    (hstep : ∀ k, x (k + 1) = x k - g (x k))
    (hdrop : ∀ k, f (x k) - f (x (k + 1)) = ‖g (x k)‖ ^ 2)
    (p : FirstOrderRegularization.Parameters) (hp : p.sigmaMin ≤ 1) :
    FirstOrderRegularization.IsRun p f g x (fun _ => 1) := by
  refine ⟨⟨hp, ?_⟩, ?_⟩
  · intro k
    rw [unitSteps_ratio_eq_one hstep hdrop k, ite_eq_left p.eta2_lt_one.le]
    exact ⟨max_le hp (by simpa only [mul_one] using p.gamma1_lt_one.le), le_rfl⟩
  · intro k
    rw [unitSteps_ratio_eq_one hstep hdrop k,
      ite_eq_left (p.eta_le.trans p.eta2_lt_one.le)]
    simpa only [FirstOrderRegularization.trial, inv_one, one_smul] using hstep k

end Optimization.LowerBound
