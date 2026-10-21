import Mathlib.Order.Filter.Extr

/-!
# Extrema under a parametrization

An extremum over an image is exactly an extremum of the composed function. No injectivity
of the parametrization is needed.
-/

open Set
variable {α β γ : Type*} [Preorder γ]

/-- Minimization over a parametrized set is equivalent to minimization in its parameters. -/
theorem isMinOn_image_iff (f : β → γ) (g : α → β) (K : Set α) (a : α) :
    IsMinOn f (g '' K) (g a) ↔ IsMinOn (f ∘ g) K a := by
  constructor
  · intro h
    exact h.comp_of_mapsTo (fun _ hx => mem_image_of_mem g hx) rfl
  · rintro h _ ⟨x, hx, rfl⟩
    exact h hx

/-- Maximization over a parametrized set is equivalent to maximization in its parameters. -/
theorem isMaxOn_image_iff (f : β → γ) (g : α → β) (K : Set α) (a : α) :
    IsMaxOn f (g '' K) (g a) ↔ IsMaxOn (f ∘ g) K a :=
  isMinOn_image_iff (γ := γᵒᵈ) f g K a
