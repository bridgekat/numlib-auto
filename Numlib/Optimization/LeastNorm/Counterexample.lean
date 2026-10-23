import Numlib.Optimization.LeastNorm.Run

/-!
# A constant-residual obstruction to an unrounded iteration count

One actual inner call solves the constant merit exactly, while the printed
real logarithmic count equals one half. Natural ceilings give the correct
integer iteration budget.
-/

namespace LeastNorm.Counterexample
open TaylorModel InexactTrustRegion
/-- The actual constant scalar residual. -/
noncomputable def residual (_ : ℝ) : ℝ := 1 / 2

/-- A primitive exact constant-objective inner solver with initialized counts. -/
def innerCall (xs : ℝ) (ε : Fin 1 → ℝ) (x : ℝ) (δ : Fin 1 → ℝ) (nf nd : ℕ) : Prop :=
  x = xs ∧ δ = (fun _ => 1) ∧ nf = 1 ∧ nd = 1 ∧ ∀ a, 0 < ε a

/-- The actual constant merit has zero first-order constrained criticality. -/
theorem constant_criticality (x : ℝ) :
    constrainedCriticality (merit residual) 1 Set.univ x 1 = 0 := by
  rw [constrainedCriticality_univ, TaylorModel.criticality_one (merit residual) x zero_lt_one]
  have hm : (merit residual : ℝ → ℝ) = fun _ => 1 / 8 := by
    funext z
    norm_num [merit, residual, Real.norm_eq_abs]
  rw [hm]
  simp

/-- The constant-objective inner solver satisfies its true criticality interface. -/
theorem inner_sound : InnerSound residual Set.univ innerCall := by
  intro xs ε x δ nf nd hc
  obtain ⟨hx, hδ, _, _, hε⟩ := hc
  subst δ
  refine ⟨Set.mem_univ _, fun _ => ⟨zero_lt_one, le_rfl⟩, fun a => ?_⟩
  have ha : modelOrder a = 1 := by unfold modelOrder; have := a.isLt; omega
  rw [ha, constant_criticality]
  exact div_nonneg (mul_nonneg (hε a).le (by positivity)) (Nat.cast_nonneg _)

/-- All primitive source rules allow exactly the initial nonterminal point and one inner call. -/
theorem one_iteration :
    Run residual Set.univ innerCall (1 / 4) (1 / 4) (fun _ => 1 / 2)
      (fun _ => 0) (fun _ _ => 1) (fun _ => 1) (fun _ => 1) 1 := by
  constructor
  · norm_num
  · norm_num
  · intro a; norm_num
  · norm_num
  · norm_num
  · norm_num [residual, Real.norm_eq_abs]
  · trivial
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num [TargetAt, residual, Real.norm_eq_abs]
  · intro k hk
    exact ⟨rfl, rfl, rfl, rfl, fun _ => by norm_num [residual, Real.norm_eq_abs]⟩

/-- The actual first target is attained at the first inner call. -/
theorem first_target_one :
    TargetAt (q := 1) residual Set.univ (1 / 4) (fun _ => 1 / 2)
      (fun _ => 0) (fun _ _ => 1) 1 ∧
      ¬TargetAt (q := 1) residual Set.univ (1 / 4) (fun _ => 1 / 2)
        (fun _ => 0) (fun _ _ => 1) 0 := by
  constructor
  · simp only [TargetAt, one_ne_zero, ite_false]
    right
    intro a
    have ha : modelOrder a = 1 := by unfold modelOrder; have := a.isLt; omega
    rw [ha, constant_criticality]
    norm_num [residual, Real.norm_eq_abs]
  · norm_num [TargetAt, residual, Real.norm_eq_abs]

/-- The literal unrounded real budget is one half and cannot bound one actual call. -/
theorem printed_iteration_bound_false :
    ¬(1 : ℝ) ≤ max 0 (Real.log ((1 / 4 : ℝ) / (1 / 2)) / Real.log (1 / 4)) := by
  have hl : Real.log (1 / 2 : ℝ) ≠ 0 := (Real.log_neg (by norm_num) (by norm_num)).ne
  have he : Real.log (1 / 4 : ℝ) = 2 * Real.log (1 / 2 : ℝ) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hr : Real.log ((1 / 4 : ℝ) / (1 / 2)) / Real.log (1 / 4) = 1 / 2 := by
    norm_num only [show (1 / 4 : ℝ) / (1 / 2) = 1 / 2 by norm_num]
    rw [he]
    field_simp
  rw [hr]
  norm_num
end LeastNorm.Counterexample
