import Numlib.Optimization.Regularization.HighOrder.CriticalityCounting

/-!
# Finite target attainment for exact high-order regularization

Consistent prefixes of the primitive algorithm reach a first finite true
optimality target or its literal zero-model-decrease exit. The proof is an
Archimedean contradiction from the derived total iteration budget.
-/

namespace HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every consistent actual execution reaches a first finite target.
No stopping index, decrease floor or iteration bound is assumed. -/
theorem exists_target {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ k < N, ¬TargetAt f P ε D k) → Run f P ε D N)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ K, TargetAt f P ε D K ∧ Run f P ε D K ∧ ∀ k < K, ¬TargetAt f P ε D k := by
  classical
  have hex : ∃ K, TargetAt f P ε D K := by
    by_contra hn
    push Not at hn
    let bound := trialCountFactor P * ((f (D.point 0) - flow) /
      (commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε) + 1) +
        trialCountOffset P L
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have h := hprefix N (fun k _ => hn k)
    exact (not_le_of_gt hN) (h.iterations_le hf hL hlip hlow (fun k _ => hn k))
  exact ⟨Nat.find hex, Nat.find_spec hex, hprefix _ (fun k hk => Nat.find_min hex hk),
    fun k hk => Nat.find_min hex hk⟩

end HighOrderRegularization
