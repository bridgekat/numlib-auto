import Mathlib.Order.Filter.Extr

/-! # Global minima under a change of variables -/

/-- A bijective change of variables preserving the objective and feasible predicate preserves
global minimizers in both directions. -/
theorem Equiv.isMinOn_iff_of_comp_eq {X Y A : Type*} [Preorder A] (e : X ≃ Y)
    (f : X → A) (g : Y → A) (p : X → Prop) (q : Y → Prop)
    (hf : ∀ x, g (e x) = f x) (hp : ∀ x, q (e x) ↔ p x) (s : X) :
    IsMinOn f {x | p x} s ↔ IsMinOn g {y | q y} (e s) := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    change g (e s) ≤ g (e x)
    rw [hf, hf]
    exact h ((hp x).mp hy)
  · intro h x hx
    have hh := h ((hp x).mpr hx)
    change g (e s) ≤ g (e x) at hh
    change f s ≤ f x
    simpa only [hf] using hh
