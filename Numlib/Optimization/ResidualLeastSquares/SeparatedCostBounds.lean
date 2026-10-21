import Numlib.Optimization.ResidualLeastSquares

/-!
# Separated maxima in residual-scaled evaluation bounds

The geometric coefficient dominates the inverse scaling weight. Its maximum and the
primal-dual tolerance maximum can therefore be separated before summing actual INNER
costs. No sum of maxima is exchanged with a maximum of sums. Initial residual queries
remain explicit; at a positive initial residual they can be absorbed into a coefficient
chosen independently of both tolerances.
-/

noncomputable section
namespace Optimization.ResidualLeastSquares

/-- The geometric coefficient for one active order, including a fixed primal scaling. -/
def geometricCostFactor (β θ p : ℝ) : ℝ :=
  β ^ (1 - 2 * p) / (β ^ (1 - p) - 1) * θ ^ (1 - p)

/-- The geometric coefficient is positive for a contraction and an exponent above one. -/
theorem geometricCostFactor_pos {β θ p : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hp : 1 < p) : 0 < geometricCostFactor β θ p := by
  have hd := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hβ hβ1 (by linarith : 1 - p < 0)
  exact mul_pos (div_pos (Real.rpow_pos_of_pos hβ _) (by linarith))
    (Real.rpow_pos_of_pos hθ _)

/-- One geometric coefficient bounds the corresponding inverse contraction weight. -/
theorem inv_rpow_le_geometricCostFactor {β θ p : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hp : 1 < p) :
    β ^ (-p) * θ ^ (1 - p) ≤ geometricCostFactor β θ p := by
  have hd := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hβ hβ1 (by linarith : 1 - p < 0)
  have hid : β ^ (1 - 2 * p) = β ^ (-p) * β ^ (1 - p) := by
    rw [← Real.rpow_add hβ]
    congr 1
    ring
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hθ.le _)
  apply (le_div_iff₀ (by linarith : 0 < β ^ (1 - p) - 1)).2
  rw [hid]
  nlinarith [Real.rpow_pos_of_pos hβ (-p)]

/-- With both fixed scales at most one, each geometric coefficient is at least one. -/
theorem one_le_geometricCostFactor {β θ p : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hp : 1 < p) :
    1 ≤ geometricCostFactor β θ p := by
  have hb : 1 ≤ β ^ (-p) :=
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hβ hβ1 (by linarith : -p < 0)).le
  have ht : 1 ≤ θ ^ (1 - p) := by
    simpa using Real.rpow_le_rpow_of_nonpos hθ hθ1 (by linarith : 1 - p ≤ 0)
  exact (one_le_mul_of_one_le_of_one_le hb ht).trans
    (inv_rpow_le_geometricCostFactor hβ hβ1 hθ hp)

/-- The largest fixed geometric coefficient over the active orders. -/
def geometricCostWeight (q : ℕ) (β θ : ℝ) (π : ℕ → ℝ) : ℝ :=
  orderMaximum q (fun j => geometricCostFactor β θ (π j))

/-- The fixed geometric weight is nonnegative, including an empty active order set. -/
theorem geometricCostWeight_nonneg (q : ℕ) (β θ : ℝ) (π : ℕ → ℝ) :
    0 ≤ geometricCostWeight q β θ π := orderMaximum_nonneg q _

/-- The primal-dual tolerance weight, separated from all fixed geometric parameters. -/
def primalDualCostWeight (q : ℕ) (ε₀ : ℝ) (ε π : ℕ → ℝ) : ℝ :=
  orderMaximum q (fun j => ε₀ ^ (1 - π j) * ε j ^ (-π j))

/-- The primal-dual tolerance weight is nonnegative. -/
theorem primalDualCostWeight_nonneg (q : ℕ) (ε₀ : ℝ) (ε π : ℕ → ℝ) :
    0 ≤ primalDualCostWeight q ε₀ ε π := orderMaximum_nonneg q _

/-- For source tolerance domains the primal-dual tolerance weight is at least one. -/
theorem one_le_primalDualCostWeight {q : ℕ} {ε₀ : ℝ} {ε π : ℕ → ℝ}
    (hq : 1 ≤ q) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) :
    1 ≤ primalDualCostWeight q ε₀ ε π := by
  have hj : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr ⟨le_rfl, hq⟩
  have hp : 1 < π 1 := hπ 1 hj
  have ha : 1 ≤ ε₀ ^ (1 - π 1) := by
    simpa using Real.rpow_le_rpow_of_nonpos hε₀ hε₀1 (by linarith : 1 - π 1 ≤ 0)
  have hb : 1 ≤ ε 1 ^ (-π 1) := by
    simpa using Real.rpow_le_rpow_of_nonpos (hε 1 hj).1 (hε 1 hj).2
      (by linarith : -π 1 ≤ 0)
  exact (one_le_mul_of_one_le_of_one_le ha hb).trans
    (le_orderMaximum (fun j => ε₀ ^ (1 - π j) * ε j ^ (-π j)) hj)

/-- Separating the fixed geometric maximum from the tolerance maximum bounds every
residual-scaled cost weight. The exponents and geometric parameters are fixed first. -/
theorem residualCostWeight_le_separated {q : ℕ} {β θ ε₀ : ℝ} {ε π : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hε₀ : 0 < ε₀)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j)
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) :
    residualCostWeight q β (θ * ε₀) ε π ≤
      geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  apply residualCostWeight_le
    (mul_nonneg (geometricCostWeight_nonneg ..) (primalDualCostWeight_nonneg ..))
  intro j hj
  calc
    β ^ (-π j) * (θ * ε₀) ^ (1 - π j) * ε j ^ (-π j) =
        (β ^ (-π j) * θ ^ (1 - π j)) *
          (ε₀ ^ (1 - π j) * ε j ^ (-π j)) := by
      rw [Real.mul_rpow hθ.le hε₀.le]
      ring
    _ ≤ geometricCostFactor β θ (π j) * (ε₀ ^ (1 - π j) * ε j ^ (-π j)) :=
      mul_le_mul_of_nonneg_right
        (inv_rpow_le_geometricCostFactor hβ hβ1 hθ (hπ j hj))
        (mul_nonneg (Real.rpow_nonneg hε₀.le _) (Real.rpow_nonneg (hε j hj) _))
    _ ≤ geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
      exact mul_le_mul
        (le_orderMaximum (fun j => geometricCostFactor β θ (π j)) hj)
        (le_orderMaximum (fun j => ε₀ ^ (1 - π j) * ε j ^ (-π j)) hj)
        (mul_nonneg (Real.rpow_nonneg hε₀.le _) (Real.rpow_nonneg (hε j hj) _))
        (geometricCostWeight_nonneg ..)

variable {E S F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {X : Set E} {r : E → F} {q : ℕ} {θ ε₀ β : ℝ}
  {ε π : ℕ → ℝ} {κ : EvaluationKind → ℝ}
  {step : (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop}
  {terminal : (ℕ → ℝ) → E × S → List EvaluationKind → Prop} {t : Trace E S}

/-- A direct separated-maxima bound for actual wrapper calls, retaining the initial
residual query explicitly and allowing the closed upper endpoint of dual tolerances. -/
theorem Execution.totalEvaluations_le_separated
    (h : Execution X r q (θ * ε₀) β ε π κ step terminal t)
    (hθ : 0 < θ) (hε₀ : 0 < ε₀) (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q (θ * ε₀) ε t k)
    (a : EvaluationKind) :
    (totalEvaluations t a K : ℝ) ≤ (if a = .function then 1 else 0) +
      (κ a / (1 - β)) / 2 * ‖r (t.point 0)‖ *
        geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  have hw := residualCostWeight_le_separated h.factor.1 h.factor.2 hθ hε₀
    (fun j hj => (h.dual j hj).1.le) hπ
  have he := h.totalEvaluations_le_uniform hbefore
    (mul_nonneg (geometricCostWeight_nonneg ..) (primalDualCostWeight_nonneg ..))
    (fun j hj => (le_residualCostWeight β (θ * ε₀) ε π hj).trans hw) a
  convert he using 1
  ring

/-- The source-shaped separated bound counts all complete INNER calls, including their
terminal events. It excludes only the separately represented initial residual query. -/
theorem Execution.evaluations_le_separated
    (h : Execution X r q (θ * ε₀) β ε π κ step terminal t)
    (hθ : 0 < θ) (hε₀ : 0 < ε₀) (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q (θ * ε₀) ε t k)
    (a : EvaluationKind) :
    (evaluations t a K : ℝ) ≤
      (κ a / (1 - β)) / 2 * ‖r (t.point 0)‖ *
        geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  have he := h.totalEvaluations_le_separated hθ hε₀ hπ hbefore a
  simp only [totalEvaluations, Nat.cast_add] at he
  cases a <;> norm_num at he ⊢ <;> linarith only [he]

/-- For a positive initial residual, the initial query is absorbed by a coefficient
fixed before both tolerances. The additional coefficient is exactly `2 / ‖r(x₀)‖`;
no uniform positive lower bound on the initial residual is assumed. -/
theorem Execution.totalEvaluations_le_separated_of_initial_pos
    (h : Execution X r q (θ * ε₀) β ε π κ step terminal t)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) (hR : 0 < ‖r (t.point 0)‖)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q (θ * ε₀) ε t k)
    (a : EvaluationKind) :
    (totalEvaluations t a K : ℝ) ≤
      (κ a / (1 - β) + 2 / ‖r (t.point 0)‖) / 2 * ‖r (t.point 0)‖ *
        geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  have hj : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr ⟨le_rfl, h.order_pos⟩
  have hG : 1 ≤ geometricCostWeight q β θ π :=
    (one_le_geometricCostFactor h.factor.1 h.factor.2 hθ hθ1 (hπ 1 hj)).trans
      (le_orderMaximum (fun j => geometricCostFactor β θ (π j)) hj)
  have hT := one_le_primalDualCostWeight h.order_pos hε₀ hε₀1 h.dual hπ
  have hGT := one_le_mul_of_one_le_of_one_le hG hT
  have he := h.totalEvaluations_le_separated hθ hε₀ hπ hbefore a
  have hinit : (if a = .function then (1 : ℝ) else 0) ≤
      geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
    split_ifs
    · exact hGT
    · exact (geometricCostWeight_nonneg q β θ π).trans
        (le_mul_of_one_le_right (geometricCostWeight_nonneg ..) hT)
  calc
    _ ≤ (if a = .function then 1 else 0) +
        (κ a / (1 - β)) / 2 * ‖r (t.point 0)‖ *
          geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := he
    _ ≤ geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π +
        (κ a / (1 - β)) / 2 * ‖r (t.point 0)‖ *
          geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π :=
      add_le_add hinit le_rfl
    _ = _ := by field_simp [hR.ne']; ring

end Optimization.ResidualLeastSquares
