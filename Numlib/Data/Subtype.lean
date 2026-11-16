/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $p$ be a predicate on a type $\alpha$, let $S = \{a \in \alpha : p(a)\}$, and let
$z \colon \alpha \to \beta$ be a function into a type with a zero. If $z$ vanishes outside $S$, then
$z$ is the extension by zero of its restriction to $S$.

## Main results

* `Function.extend_val_comp_val`: a function that vanishes outside $S$ is the extension by zero of
  its restriction to $S$.
-/

namespace Function

/-- Let $\beta$ be a type with a zero, let $p$ be a predicate on $\alpha$ with
$S = \{a \in \alpha : p(a)\}$, and let $z \colon \alpha \to \beta$ satisfy $z(a) = 0$ for every
$a \notin S$. Then $z$ is the **extension by zero** of its restriction $z|_S$: the function that
equals $z|_S$ on $S$ and $0$ outside $S$ is $z$.

The extension by zero is `Function.extend Subtype.val (z ∘ Subtype.val) 0`, where `Subtype.val`
is the inclusion of the subtype `{a // p a}` in $\alpha$. -/
theorem extend_val_comp_val {α β : Type*} [Zero β] {p : α → Prop} {z : α → β}
    (hz : ∀ a, ¬ p a → z a = 0) :
    extend (Subtype.val : {a // p a} → α) (z ∘ Subtype.val) 0 = z := by
  funext a
  by_cases ha : p a
  · exact Subtype.val_injective.extend_apply _ _ ⟨a, ha⟩
  · rw [extend_apply' _ _ _ (fun ⟨b, hb⟩ => ha (hb ▸ b.2)), hz a ha, Pi.zero_apply]

end Function
