import Numlib.Optimization.TrustRegion.Inexact.Selection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fixed-cost simulation of derivative evaluation schedules

Every simulated evaluation consists of an actual finite list of lower-order
oracle calls. A common list-length cap is chosen before requested accuracies.
Summing those primitive calls transfers derivative evaluation budgets without
assuming any aggregate oracle complexity in the execution data.
-/

namespace OracleSimulation

/-- Total primitive calls in finite batches for each requested derivative order.
The `Fin (o+1)` labels ensure every primitive oracle has degree at most `o`. -/
def calls {p o : ℕ} (evaluations : Fin (p + 1) → ℕ)
    (batch : Fin (p + 1) → ℕ → List (Fin (o + 1))) : ℕ :=
  ∑ i, ∑ k ∈ Finset.range (evaluations i), (batch i k).length

/-- A fixed per-evaluation stencil cap bounds the total number of actual
lower-order oracle calls by that cap times the total number of evaluations. -/
theorem calls_le {p o : ℕ} (evaluations : Fin (p + 1) → ℕ)
    (batch : Fin (p + 1) → ℕ → List (Fin (o + 1))) (C : ℕ)
    (hbatch : ∀ i k, k < evaluations i → (batch i k).length ≤ C) :
    calls evaluations batch ≤ C * ∑ i, evaluations i := by
  unfold calls
  calc _ ≤ ∑ i, ∑ _k ∈ Finset.range (evaluations i), C := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun k hk => hbatch i k (Finset.mem_range.mp hk)
    _ = C * ∑ i, evaluations i := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Separate objective and positive-order evaluation budgets give the literal
fixed-stencil oracle-call budget. Primitive labels remain degree at most `o`. -/
theorem calls_le_function_derivative {p o : ℕ} (evaluations : Fin (p + 1) → ℕ)
    (batch : Fin (p + 1) → ℕ → List (Fin (o + 1))) (C F D : ℕ)
    (hbatch : ∀ i k, k < evaluations i → (batch i k).length ≤ C)
    (hF : evaluations 0 ≤ F) (hD : ∀ i : Fin p, evaluations i.succ ≤ D) :
    calls evaluations batch ≤ C * (F + p * D) := by
  apply (calls_le evaluations batch C hbatch).trans
  apply Nat.mul_le_mul_left
  rw [Fin.sum_univ_succ]
  apply Nat.add_le_add hF
  calc _ ≤ ∑ _i : Fin p, D := Finset.sum_le_sum fun i _ => hD i
    _ = p * D := by simp

/-- The logarithmic accuracy overhead is dominated by any fixed positive
inverse-accuracy power, including the unit-accuracy endpoint. -/
theorem abs_log_le_inverse_power {μ r : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hr : 0 < r) : |Real.log μ| ≤ μ ^ (-r) / r := by
  have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hμ (-r))
  rw [Real.log_rpow hμ] at hh
  rw [abs_of_nonpos (Real.log_nonpos hμ.le hμ1)]
  apply (le_div_iff₀ hr).mpr
  nlinarith

/-- The minimum component controls the finite minimum of arbitrary positive
accuracy powers, with the largest exponent fixed independently of accuracies. -/
theorem minimum_power_lower {q : ℕ} (hq : 0 < q) (ε exponent : Fin q → ℝ)
    {R : ℝ} (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1)
    (hexp : ∀ a, 0 ≤ exponent a ∧ exponent a ≤ R) :
    InexactTrustRegion.minimumAccuracy hq ε ^ R ≤
      InexactTrustRegion.minimumAccuracy hq (fun a => ε a ^ exponent a) := by
  have hμ := InexactTrustRegion.minimumAccuracy_pos hq hε
  have hμ1 := (InexactTrustRegion.minimumAccuracy_le hq ε ⟨0, hq⟩).trans (hε1 _)
  apply Finset.le_inf'
  intro a _
  exact (Real.rpow_le_rpow_of_exponent_ge hμ hμ1 (hexp a).2).trans
    (Real.rpow_le_rpow hμ.le (InexactTrustRegion.minimumAccuracy_le hq ε a) (hexp a).1)

end OracleSimulation

namespace OracleSimulation

/-- The literal derivative-order schedule contains the objective budget at zero
and the common derivative budget in every positive order. -/
def schedule (p F D : ℕ) : Fin (p + 1) → ℕ := fun i => if i = 0 then F else D

/-- Fixed-cost primitive batches inherit separate objective and derivative
budgets without presuming any total oracle-call bound. -/
theorem calls_schedule_le {p o : ℕ} (F D C : ℕ)
    (batch : Fin (p + 1) → ℕ → List (Fin (o + 1)))
    (hbatch : ∀ i k, k < schedule p F D i → (batch i k).length ≤ C) :
    calls (schedule p F D) batch ≤ C * (F + p * D) := by
  apply calls_le_function_derivative _ _ C F D hbatch
  · simp only [schedule, ite_true, le_refl]
  · intro i
    simp only [schedule, Fin.succ_ne_zero, ite_false, le_refl]

/-- Positive inverse powers absorb the logarithmic request overhead and the
fixed setup costs. All coefficients, stencil costs and the rate precede accuracy. -/
theorem exists_calls_inverse_power_bound (p C : ℕ) {A B F₀ D₀ gap R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F₀) (hD : 0 ≤ D₀)
    (hgap : 0 ≤ gap) (hR : 0 < R) :
    ∃ κ > 0, ∀ μ φ : ℝ, 0 < μ → μ ≤ 1 → μ ^ R ≤ φ →
      ∀ F D : ℕ,
        (F : ℝ) ≤ A * gap / φ + B * |Real.log μ| + F₀ →
        (D : ℝ) ≤ A * gap / φ + B * |Real.log μ| + D₀ →
        ∀ (o : ℕ) (batch : Fin (p + 1) → ℕ → List (Fin (o + 1))),
          (∀ i k, k < schedule p F D i → (batch i k).length ≤ C) →
          (calls (schedule p F D) batch : ℝ) ≤ κ * μ ^ (-R) := by
  let K := (C : ℝ) * (((p : ℝ) + 1) * (A * gap + B / R) + F₀ + p * D₀)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro μ φ hμ hμ1 hφ F D hFb hDb o batch hbatch
  have hp := Real.rpow_pos_of_pos hμ R
  have hpower : 1 ≤ μ ^ (-R) := by
    rw [Real.rpow_neg hμ.le]
    exact (one_le_inv₀ hp).mpr (Real.rpow_le_one hμ.le hμ1 hR.le)
  have hr : A * gap / φ ≤ A * gap * μ ^ (-R) := by
    rw [Real.rpow_neg hμ.le]
    exact div_le_div_of_nonneg_left (mul_nonneg hA hgap) hp hφ
  have hlog := mul_le_mul_of_nonneg_left (abs_log_le_inverse_power hμ hμ1 hR) hB
  have hlog' : B * |Real.log μ| ≤ (B / R) * μ ^ (-R) := by
    convert hlog using 1; ring
  have hFconst := mul_le_mul_of_nonneg_left hpower hF
  have hDconst := mul_le_mul_of_nonneg_left hpower hD
  have hF' : (F : ℝ) ≤ (A * gap + B / R + F₀) * μ ^ (-R) := by
    nlinarith [hFb]
  have hD' : (D : ℝ) ≤ (A * gap + B / R + D₀) * μ ^ (-R) := by
    nlinarith [hDb]
  have hb : (calls (schedule p F D) batch : ℝ) ≤ (C : ℝ) * (F + p * D) := by
    exact_mod_cast calls_schedule_le F D C batch hbatch
  have hsum := add_le_add hF' (mul_le_mul_of_nonneg_left hD' (Nat.cast_nonneg p))
  have hscaled := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg C)
  have he : (C : ℝ) * ((A * gap + B / R + F₀) * μ ^ (-R) +
      p * ((A * gap + B / R + D₀) * μ ^ (-R))) = K * μ ^ (-R) := by
    dsimp [K]
    ring
  rw [he] at hscaled
  apply hb.trans (hscaled.trans _)
  exact mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (Real.rpow_nonneg hμ.le _)

end OracleSimulation
