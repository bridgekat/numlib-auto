/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Subtype`, beside `Function.extend_val_apply`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Subtype

/-!
# Extending a restriction by zero

`Function.extend_val_comp_val`: a function vanishing off `p` is the extension by zero of its
restriction to `{a // p a}`.
-/

namespace Function

/-- **A function vanishing off `p` is the extension by zero of its restriction** to
`{a // p a}`. -/
theorem extend_val_comp_val {α β : Type*} [Zero β] {p : α → Prop} {z : α → β}
    (hz : ∀ a, ¬ p a → z a = 0) :
    extend (Subtype.val : {a // p a} → α) (z ∘ Subtype.val) 0 = z := by
  funext a
  by_cases ha : p a
  · exact Subtype.val_injective.extend_apply _ _ ⟨a, ha⟩
  · rw [extend_apply' _ _ _ (fun ⟨b, hb⟩ => ha (hb ▸ b.2)), hz a ha, Pi.zero_apply]

end Function
