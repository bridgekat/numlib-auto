import Numlib.Optimization.LeastNorm.Budget

/-!
# The source-shaped feasibility-phase evaluation budget

The section's explicit per-call INNER cost and endpoint contracts imply a
complete least-norm outer budget. Constants are fixed before primal and dual
accuracies. A positive change of the per-call constant puts the valid geometric
sum estimate in the two-maximum form used for the feasibility phase.
-/

noncomputable section
namespace LeastNorm
open scoped BigOperators

/-- Products of nonnegative weights are controlled by the product of their
actual finite maxima; no maximizing order is assumed to be common. -/
theorem maximumWeight_mul_le {q : ℕ} (hq : 0 < q) {u v : Fin q → ℝ}
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) :
    maximumWeight hq (fun a => u a * v a) ≤ maximumWeight hq u * maximumWeight hq v := by
  apply maximumWeight_le
  intro a
  exact mul_le_mul (le_maximumWeight hq u a) (le_maximumWeight hq v a) (hv a)
    (maximumWeight_nonneg hq hu)

/-- The source's finite geometric coefficient, independent of all accuracies. -/
def phaseOneFactor {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ) (β θ : ℝ) : ℝ :=
  maximumWeight hq (fun a => β ^ (1 - 2 * π a) /
    (β ^ (1 - π a) - 1) * θ ^ (1 - π a))

/-- Every source geometric coefficient is strictly positive. -/
theorem phaseOneFactor_pos {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ)
    (hπ : ∀ a, 1 < π a) {β θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) :
    0 < phaseOneFactor hq π β θ := by
  let a : Fin q := ⟨0, hq⟩
  have hd : 0 < β ^ (1 - π a) - 1 := by
    have hh := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hβ hβ1
      (show 1 - π a < 0 by linarith [hπ a])
    linarith
  have hp : 0 < β ^ (1 - 2 * π a) / (β ^ (1 - π a) - 1) * θ ^ (1 - π a) :=
    mul_pos (div_pos (Real.rpow_pos_of_pos hβ _) hd) (Real.rpow_pos_of_pos hθ _)
  exact hp.trans_le (le_maximumWeight hq
    (fun a => β ^ (1 - 2 * π a) / (β ^ (1 - π a) - 1) * θ ^ (1 - π a)) a)

/-- The fixed envelope in the valid finite geometric-sum bound. -/
def phaseOneEnvelope {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ) (β θ : ℝ) : ℝ :=
  maximumWeight hq (fun a => β ^ (-π a) * θ ^ (1 - π a))

/-- The fixed envelope is strictly positive for positive scales. -/
theorem phaseOneEnvelope_pos {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ)
    {β θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ) : 0 < phaseOneEnvelope hq π β θ := by
  let a : Fin q := ⟨0, hq⟩
  have hp : 0 < β ^ (-π a) * θ ^ (1 - π a) :=
    mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos hθ _)
  exact hp.trans_le (le_maximumWeight hq (fun a => β ^ (-π a) * θ ^ (1 - π a)) a)

/-- A positive rescaling of an INNER cost constant, fixed before every primal
and dual tolerance, gives the source's exact two-maximum coefficient. -/
def phaseOneConstant {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ) (β θ κ : ℝ) : ℝ :=
  max κ (κ * phaseOneEnvelope hq π β θ / ((1 - β) * phaseOneFactor hq π β θ))

/-- The source-shaped constant is at least the known per-call constant. -/
theorem le_phaseOneConstant {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ) (β θ κ : ℝ) :
    κ ≤ phaseOneConstant hq π β θ κ := le_max_left _ _

/-- A positive known per-call constant gives a positive source-shaped constant. -/
theorem phaseOneConstant_pos {q : ℕ} (hq : 0 < q) (π : Fin q → ℝ)
    (β θ : ℝ) {κ : ℝ} (hκ : 0 < κ) : 0 < phaseOneConstant hq π β θ κ :=
  hκ.trans_le (le_phaseOneConstant hq π β θ κ)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- Genuine INNER counts need only hold for feasible starts in the fixed
initial residual level. This is the section's per-call cost contract, not a
conclusion about the total feasibility-phase cost. -/
def InnerCountsOn {q : ℕ} (r : E → F) (X : Set E) (R : ℝ)
    (call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop)
    (hq : 0 < q) (π : Fin q → ℝ) (κF κD : ℝ) : Prop :=
  ∀ xs ∈ X, ‖r xs‖ ≤ R → ∀ tol y δ nf nd, call xs tol y δ nf nd →
    (nf : ℝ) ≤ κF * merit r xs * maximumWeight hq (fun a => (tol a) ^ (-π a)) ∧
    (nd : ℝ) ≤ κD * merit r xs * maximumWeight hq (fun a => (tol a) ^ (-π a))

namespace Run
variable {q : ℕ} {r : E → F} {X : Set E}
  {call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop}
  {ε₀ β θ : ℝ} {ε : Fin q → ℝ} {x : ℕ → E} {δ : ℕ → Fin q → ℝ}
  {nf nd : ℕ → ℕ} {N : ℕ}

/-- Every outer point is feasible, by initialization and actual inner-call soundness. -/
theorem feasible (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) {k : ℕ} (hk : k ≤ N) : x k ∈ X := by
  cases k with
  | zero => exact h.initial_feasible
  | succ k => exact (hsound _ _ _ _ _ _ (h.inner k (by omega))).1

/-- Every nonterminal inner starting point lies in the fixed initial residual level. -/
theorem residual_le_initial (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) {k : ℕ} (hk : k < N) : ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  have hp := pow_le_one₀ h.contraction_pos.le h.contraction_lt_one.le (n := k)
  exact (h.residual_le_geometric hsound hk).trans
    (mul_le_of_le_one_right (norm_nonneg _) hp)

/-- The entire actual feasibility run has the displayed two-maximum bound.
The changed constant is positive and independent of both accuracy vectors. -/
theorem evaluations_le_phaseOne (h : Run r X call (θ * ε₀) β ε x δ nf nd N)
    (hsound : InnerSound r X call) (hq : 0 < q) (π : Fin q → ℝ)
    (hπ : ∀ a, 1 < π a) (hθ : 0 < θ) (hε₀ : 0 < ε₀)
    {κ : ℝ} (hκ : 0 ≤ κ) (count : ℕ → ℕ)
    (hcount : ∀ k < N, (count k : ℝ) ≤ κ * merit r (x k) *
      maximumWeight hq (fun a => (β * ‖r (x k)‖ * ε a) ^ (-π a))) :
    (∑ k ∈ Finset.range N, (count k : ℝ)) ≤
      phaseOneConstant hq π β θ κ / 2 * ‖r (x 0)‖ * phaseOneFactor hq π β θ *
        maximumWeight hq (fun a => ε₀ ^ (1 - π a) * ε a ^ (-π a)) := by
  have hbase := h.evaluations_le hsound hq π hπ hκ count hcount
  have he : (fun a : Fin q => β ^ (-π a) * (θ * ε₀) ^ (1 - π a) * ε a ^ (-π a)) =
      (fun a => (β ^ (-π a) * θ ^ (1 - π a)) *
        (ε₀ ^ (1 - π a) * ε a ^ (-π a))) := by
    funext a
    rw [Real.mul_rpow hθ.le hε₀.le]
    ring
  rw [he] at hbase
  have hm := maximumWeight_mul_le hq
    (u := fun a => β ^ (-π a) * θ ^ (1 - π a))
    (v := fun a => ε₀ ^ (1 - π a) * ε a ^ (-π a))
    (fun a => mul_nonneg (Real.rpow_nonneg h.contraction_pos.le _)
      (Real.rpow_nonneg hθ.le _))
    (fun a => mul_nonneg (Real.rpow_nonneg hε₀.le _)
      (Real.rpow_nonneg (h.accuracy a).1.le _))
  have hc : 0 ≤ κ / 2 * ‖r (x 0)‖ / (1 - β) := by
    exact div_nonneg (mul_nonneg (div_nonneg hκ (by norm_num)) (norm_nonneg _))
      (sub_pos.mpr h.contraction_lt_one).le
  apply hbase.trans
  apply (mul_le_mul_of_nonneg_left hm hc).trans
  have hF := phaseOneFactor_pos hq π hπ h.contraction_pos h.contraction_lt_one hθ
  have hW : 0 ≤ maximumWeight hq (fun a => ε₀ ^ (1 - π a) * ε a ^ (-π a)) :=
    maximumWeight_nonneg hq (fun a => mul_nonneg (Real.rpow_nonneg hε₀.le _)
      (Real.rpow_nonneg (h.accuracy a).1.le _))
  calc
    _ = (κ * phaseOneEnvelope hq π β θ /
        ((1 - β) * phaseOneFactor hq π β θ)) / 2 * ‖r (x 0)‖ *
          phaseOneFactor hq π β θ *
            maximumWeight hq (fun a => ε₀ ^ (1 - π a) * ε a ^ (-π a)) := by
      unfold phaseOneEnvelope
      have hn := hF.ne'
      have hb : 1 - β ≠ 0 := (sub_pos.mpr h.contraction_lt_one).ne'
      field_simp
    _ ≤ _ := by
      unfold phaseOneConstant
      gcongr
      exact le_max_right _ _

/-- Every associated endpoint radius is legal, using actual inner-call
soundness or the freely assigned legal radii of an immediate primal exit. -/
theorem radius_mem (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) (hδ₀ : ∀ a, 0 < δ 0 a ∧ δ 0 a ≤ 1)
    (a : Fin q) : 0 < δ N a ∧ δ N a ≤ 1 := by
  cases N with
  | zero => exact hδ₀ a
  | succ N => exact (hsound _ _ _ _ _ _ (h.inner N (by omega))).2.1 a

end Run

/-- The known per-call INNER contracts yield uniform source-shaped phase-one
constants before every primal and dual accuracy, and an actual first outer
return with legal associated radii. The cost contract is required only on the
fixed initial residual level. -/
theorem exists_phaseOne_budget {q : ℕ} {r : E → F} {X : Set E}
    {call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop}
    (hsound : InnerSound r X call) (hq : 0 < q) (π : Fin q → ℝ)
    (hπ : ∀ a, 1 < π a) (x₀ : E) {β θ κF κD : ℝ}
    (_hβ : 0 < β) (_hβ1 : β < 1) (hθ : 0 < θ) (hκF : 0 < κF) (hκD : 0 < κD)
    (hcounts : InnerCountsOn r X ‖r x₀‖ call hq π κF κD) :
    ∃ KF > 0, ∃ KD > 0, ∀ (ε₀ : ℝ) (_hε₀ : 0 < ε₀)
      (ε : Fin q → ℝ) (x : ℕ → E) (δ : ℕ → Fin q → ℝ) (nf nd : ℕ → ℕ),
      x 0 = x₀ → (∀ a, 0 < δ 0 a ∧ δ 0 a ≤ 1) →
      (∀ N, (∀ k < N, ¬TargetAt r X (θ * ε₀) ε x δ k) →
        Run r X call (θ * ε₀) β ε x δ nf nd N) →
      ∃ K, Run r X call (θ * ε₀) β ε x δ nf nd K ∧
        (∀ k < K, ¬TargetAt r X (θ * ε₀) ε x δ k) ∧
        (∀ a, 0 < δ K a ∧ δ K a ≤ 1) ∧
        (‖r (x K)‖ ≤ θ * ε₀ ∨ ∀ a,
          TaylorModel.constrainedCriticality (merit r) (InexactTrustRegion.modelOrder a)
            X (x K) (δ K a) ≤ ε a * ‖r (x K)‖ *
              δ K a ^ InexactTrustRegion.modelOrder a /
                (InexactTrustRegion.modelOrder a).factorial) ∧
        (∑ k ∈ Finset.range K, (nf k : ℝ)) ≤
          KF / 2 * ‖r x₀‖ * phaseOneFactor hq π β θ *
          maximumWeight hq (fun a => ε₀ ^ (1 - π a) * ε a ^ (-π a)) ∧
        (∑ k ∈ Finset.range K, (nd k : ℝ)) ≤
          KD / 2 * ‖r x₀‖ * phaseOneFactor hq π β θ *
          maximumWeight hq (fun a => ε₀ ^ (1 - π a) * ε a ^ (-π a)) := by
  refine ⟨phaseOneConstant hq π β θ κF, phaseOneConstant_pos hq π β θ hκF,
    phaseOneConstant hq π β θ κD, phaseOneConstant_pos hq π β θ hκD, ?_⟩
  intro ε₀ hε₀ ε x δ nf nd hx hδ hprefix
  obtain ⟨K, ht, hr, hfirst, _⟩ := exists_first_target hsound hprefix
  have hc (k : ℕ) (hk : k < K) := hcounts (x k) (hr.feasible hsound hk.le)
    (by simpa only [hx] using hr.residual_le_initial hsound hk)
      _ _ _ _ _ (hr.inner k hk)
  refine ⟨K, hr, hfirst, hr.radius_mem hsound hδ, ?_, ?_, ?_⟩
  · by_cases hk : K = 0
    · subst K
      exact Or.inl (by simpa only [TargetAt, ite_true] using ht)
    · simpa only [TargetAt, hk, ite_false] using ht
  · simpa only [hx] using hr.evaluations_le_phaseOne hsound hq π hπ hθ hε₀ hκF.le nf
      (fun k hk => (hc k hk).1)
  · simpa only [hx] using hr.evaluations_le_phaseOne hsound hq π hπ hθ hε₀ hκD.le nd
      (fun k hk => (hc k hk).2)

end LeastNorm
