import Numlib.Optimization.Regularization.Constrained.Run

/-!
# Attaining constrained optimality checks

Compact feasible balls supply genuine Taylor directions. The first failed
computed test is selected in finite order; no check outcome is assumed.
-/

namespace ConstrainedRegularization
open Set InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exact feasible criticality directions always define an ordered relative
optimality check, including the selected-none return. -/
theorem exists_optimalityCheck {q : ℕ} (f : E → ℝ) {X : Set E}
    (hX : IsClosed X) {x : E} (hx : x ∈ X) {ζ : ℝ} (hζ : ζ ≤ 1)
    (ε δ : Fin q → ℝ) (hδ : ∀ a, 0 ≤ δ a) :
    ∃ (d : Fin q → E) (selected : Option (Fin q)),
      HighOrderRegularization.ConstrainedOptimalityCheck f X ζ ε δ x d selected := by
  classical
  have hex : ∀ a : Fin q, ∃ d : E, x + d ∈ X ∧ ‖d‖ ≤ δ a ∧
      TaylorModel.decrement f (modelOrder a) x d =
        TaylorModel.constrainedCriticality f (modelOrder a) X x (δ a) :=
    fun a => TaylorModel.exists_decrement_eq_constrainedCriticality f (modelOrder a) hX hx
      (hδ a)
  choose d hd using hex
  let bad (a : Fin q) : Prop := ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial ≤
    TaylorModel.decrement f (modelOrder a) x (d a)
  have happ : ∀ a, ζ * TaylorModel.constrainedCriticality f (modelOrder a) X x (δ a) ≤
      TaylorModel.decrement f (modelOrder a) x (d a) := by
    intro a
    rw [(hd a).2.2]
    exact mul_le_of_le_one_left
      (TaylorModel.constrainedCriticality_nonneg f (modelOrder a) hX hx (hδ a)) hζ
  by_cases hbad : ∃ a, bad a
  · let S := Finset.univ.filter bad
    have hS : S.Nonempty := by obtain ⟨a, ha⟩ := hbad; exact ⟨a, by simp [S, ha]⟩
    let a := S.min' hS
    have ha : bad a := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    refine ⟨d, some a, ?_⟩
    refine ⟨fun b _ => ⟨(hd b).1, (hd b).2.1⟩, fun b _ => happ b, ?_, ?_, ?_⟩
    · intro hn
      contradiction
    · intro b hb
      have he : a = b := Option.some.inj hb
      simpa only [he] using ha
    · intro b hb c hcb
      have he : a = b := Option.some.inj hb
      apply lt_of_not_ge
      intro hc
      have hcS : c ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hh := Finset.min'_le S c hcS
      omega
  · refine ⟨d, none, ?_⟩
    refine ⟨fun a _ => ⟨(hd a).1, (hd a).2.1⟩, fun a _ => happ a, ?_, ?_, ?_⟩
    · intro _ a
      exact lt_of_not_ge (fun ha => hbad ⟨a, ha⟩)
    · intro a ha
      contradiction
    · intro a ha
      contradiction

end ConstrainedRegularization
