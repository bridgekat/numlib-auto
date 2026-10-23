import Numlib.Optimization.Regularization.HighOrder.CriticalityRun

/-!
# True optimality at exact high-order regularization targets

A literal zero-decrease approximate-global solve makes zero a genuine global
model minimum. Finite local model regularity then certifies true objective
criticality on positive radii. The low-order case cannot reach this exit after
a failed actual Step1 check.
-/

namespace HighOrderRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every literal target of the actual execution certifies true all-order
approximate optimality. In the low-order case its actual inherited radii
already certify the target; a zero-decrease exit is impossible. -/
theorem Run.target_optimality (h : Run f P ε D N) (hf : ContDiffAt ℝ p f (D.point N))
    (htarget : TargetAt f P ε D N) :
    ∃ δ : Fin q → ℝ, OptimalityAt f ε (D.point N) δ ∧ (q ≤ 2 → δ = D.radius N) := by
  classical
  rcases htarget with hopt | ⟨hselected, hzero⟩
  · exact ⟨D.radius N, hopt, fun _ => rfl⟩
  · have hcheck := h.check N le_rfl
    obtain ⟨μ, hμ, _, hsolve⟩ := (h.step_two N le_rfl hselected).fraction
    cases hsel : D.selected N with
    | none => exact (hselected hsel).elim
    | some a =>
      have hguard : ∀ b, D.selected N = some b → a ≤ b := by
        intro b hb
        have hab : a = b := Option.some.inj (hsel.symm.trans hb)
        exact hab.le
      have hfeasa := hcheck.feasible a hguard
      let d : Fin q → E := fun b =>
        if ‖D.direction N b‖ ≤ D.radius N b then D.direction N b else 0
      have hfeas : ∀ b, ‖d b‖ ≤ D.radius N b := by
        intro b
        dsimp [d]
        split_ifs with hb
        · exact hb
        · simpa only [norm_zero] using (h.radius_mem le_rfl b).1.le
      have hfailed : ∃ b, P.zeta * ε b * D.radius N b ^ modelOrder b /
          (modelOrder b).factorial ≤
            TaylorModel.decrement f (modelOrder b) (D.point N) (d b) := by
        refine ⟨a, ?_⟩
        simpa only [d, ite_eq_left hfeasa] using hcheck.failed a hsel
      obtain ⟨hq3, δ, hδ, hcrit⟩ := zero_step_termination P.order_le hf hμ hsolve hzero
        ε (D.radius N) h.accuracy_pos (fun b => (h.radius_mem le_rfl b).1)
        d hfeas P.zeta_pos hfailed
      exact ⟨δ, ⟨hδ, hcrit⟩, fun hq2 => by omega⟩

end HighOrderRegularization
