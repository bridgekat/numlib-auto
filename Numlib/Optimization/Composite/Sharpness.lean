import Numlib.Optimization.Composite.SmoothExecution
import Numlib.Optimization.Composite.RunBudget
import Numlib.Optimization.Regularization.HighOrder.Sharpness.CriticalityWitness

/-!
# Genuine first-order composite evaluation lower bounds

Globally bounded smooth Hermite objectives embed into the composite class with
a zero residual and the nonzero convex outer function absolute value. Actual
regularization executions, computed step tests and the complete evaluation
schedule are preserved. Their first true unit-radius certificate requires the
source inverse-accuracy order, with problem constants fixed before accuracy.
-/

namespace Composite
open InexactTrustRegion

/-- Fixed legal composite settings and uniform problem constants precede all
accuracies. Actual first-order runs attain the inverse-accuracy lower bound
for iterations and every scalar/residual derivative evaluation schedule. -/
theorem exists_first_order_sharpness {p : ℕ} (hp : 1 ≤ p) :
    ∃ P : Settings p 1, ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (f : ℝ → ℝ) (D : ExecutionData ℝ 1) (N : ℕ),
        ContDiff ℝ p f ∧ (∀ x, |f x| ≤ B) ∧
        (∀ j ≤ p, ∀ x y,
          ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖) ∧
        Run f (fun _ : ℝ => (0 : ℝ)) abs P (fun _ => ε) D N ∧
        StrictMono D.point ∧ D.selected N = none ∧
        (∀ k a, D.radius k a = 1 ∧ D.solvedRadius k a = 1) ∧
        criticality f (fun _ : ℝ => (0 : ℝ)) abs 1 (D.point N) 1 ≤ ε ∧
        (∀ k < N, ε < criticality f (fun _ : ℝ => (0 : ℝ)) abs 1 (D.point k) 1) ∧
        ε ^ (-((p + 1 : ℕ) : ℝ) / p) ≤ (N : ℝ) ∧
        functionEvaluations N = N + 1 ∧
        ∀ j, 1 ≤ j → j ≤ p →
          ε ^ (-((p + 1 : ℕ) : ℝ) / p) ≤
            ((HighOrderRegularization.Sharpness.derivativeEvaluationNodes
              D.selected j N).card : ℝ) := by
  let P := HighOrderRegularization.Sharpness.criticalitySettings
    (p := p) (q := 1) (by norm_num) hp
  obtain ⟨L, B, hL, hB, hex⟩ :=
    HighOrderRegularization.Sharpness.exists_low_order_criticality_witness
      (p := p) (q := 1) (by norm_num) hp (by norm_num)
  refine ⟨P, L, B, hL, hB, ?_⟩
  intro ε hε hεhalf
  obtain ⟨f, hf, hb, hLip, hr, hmono, hsel, hcrit, hprev, hN, hfun, hder⟩ :=
    hex ε hε hεhalf
  let u := (2 : ℝ) / 3 * ε
  let N := HighOrderRegularization.Sharpness.length p 1 u
  let t := HighOrderRegularization.Sharpness.step p 1 u
  let D := HighOrderRegularization.Sharpness.criticalityData p 1 N (by norm_num) t
  have hstrict : ∀ k ≤ N, ∀ a : Fin 1, D.selected k = some a →
      P.zeta * ε * D.radius k a ^ modelOrder a / (modelOrder a).factorial <
        TaylorModel.decrement f (modelOrder a) (D.point k) (D.direction k a) := by
    intro k hk a ha
    have hkN : k < N := by
      by_contra hn
      have he : k = N := by omega
      subst k
      simp only [D, HighOrderRegularization.Sharpness.criticalityData,
        lt_self_iff_false, ite_false, reduceCtorEq] at ha
    have hg : ∀ b, D.selected k = some b → a ≤ b := fun b _ =>
      le_of_eq (Subsingleton.elim _ _)
    have hh := (hr.check k hk).approximation a hg
    have hj : modelOrder a = 1 := by unfold modelOrder; omega
    change (1 : ℝ) * TaylorModel.criticality f (modelOrder a) (D.point k) 1 ≤
      TaylorModel.decrement f (modelOrder a) (D.point k) (D.direction k a) at hh
    simp only [one_mul, hj] at hh
    have hfailing := hprev k hkN
    simp only [Nat.factorial_one, Nat.cast_one, div_one] at hfailing
    change TaylorModel.criticality f 1 (D.point k) 1 > ε at hfailing
    simpa only [P, D, HighOrderRegularization.Sharpness.criticalitySettings,
      HighOrderRegularization.Sharpness.criticalityData, hj, pow_one,
      Nat.factorial_one, Nat.cast_one, div_one, one_mul, mul_one] using hfailing.trans_le hh
  obtain ⟨C, he, hC⟩ := exists_run_of_smooth (F := ℝ) abs_zero hr hstrict
  have hpoint : C.point = D.point := congrArg HighOrderRegularization.ExecutionData.point he
  have hselected : C.selected = D.selected :=
    congrArg HighOrderRegularization.ExecutionData.selected he
  have hradius : C.radius = D.radius :=
    congrArg HighOrderRegularization.ExecutionData.radius he
  have hsolved : C.solvedRadius = D.solvedRadius :=
    congrArg HighOrderRegularization.ExecutionData.solvedRadius he
  refine ⟨f, C, N, hf, hb, hLip, hC, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rwa [hpoint]
  · rwa [hselected]
  · intro k a
    rw [hradius, hsolved]
    exact ⟨rfl, rfl⟩
  · rw [hpoint, criticality_zero_residual f abs_zero]
    simpa only [modelOrder, Fin.val_zero, zero_add, Nat.factorial_one, Nat.cast_one,
      div_one] using hcrit (0 : Fin 1)
  · intro k hk
    rw [hpoint, criticality_zero_residual f abs_zero]
    simpa only [Nat.factorial_one, Nat.cast_one, div_one] using hprev k hk
  · simpa only [Nat.sub_add_cancel hp] using hN
  · intro j hj hjp
    rw [hselected, ←(hder j hj hjp).1]
    simpa only [Nat.sub_add_cancel hp] using (hder j hj hjp).2.2

end Composite
