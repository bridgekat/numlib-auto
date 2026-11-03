import Mathlib.Basic.Real.Basic
import Numlib.Krylov.Subspace

/-!
# The Lanczos basis

Section 5.2 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter05

open Krylov

/-- Lemma 5.2.1. A basis of nested Krylov spaces can add the next vector using
the previous space and the image of its last vector. The argument uses the
successive spans and requires no normalization. -/
theorem lemma_5_2_1 {E : Type*} [AddCommGroup E] [Module ℝ E]
    (H : E →ₗ[ℝ] E) (q : ℕ → E) {k i : ℕ} (hi : i ≤ k)
    (hspan : ∀ j ≤ k + 1,
      subspace H (q 0) (j + 1) = Submodule.span ℝ (Set.range fun l : Fin (j + 1) => q l)) :
    q (i + 1) ∈ Submodule.span ℝ (Set.range fun l : Fin (i + 1) => q l) ⊔
      Submodule.span ℝ {H (q i)} := by
  let K := subspace H (q 0) (i + 1)
  let W := K ⊔ Submodule.span ℝ {H (q i)}
  have hK : K ≤ W := le_sup_left
  have hmap : K.map H ≤ W := by
    change (subspace H (q 0) (i + 1)).map H ≤ W
    rw [hspan i (by omega), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases (Nat.le_of_lt_succ j.isLt).lt_or_eq with hj | hj
    · have hqj : q j ∈ subspace H (q 0) i := by
        cases i with
        | zero => omega
        | succ l =>
          rw [hspan l (by omega)]
          exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      exact hK (map_subspace_le H (q 0) i ⟨_, hqj, rfl⟩)
    · apply Submodule.mem_sup_right
      change H (q j) ∈ Submodule.span ℝ {H (q i)}
      rw [hj]
      exact Submodule.mem_span_singleton_self _
  have hnext : subspace H (q 0) (i + 1 + 1) ≤ W := by
    rw [subspace_succ_eq_sup_map H (q 0) (Nat.succ_pos i)]
    exact sup_le hK hmap
  have hq : q (i + 1) ∈ subspace H (q 0) (i + 1 + 1) := by
    rw [hspan (i + 1) (by omega)]
    exact Submodule.subset_span ⟨⟨i + 1, Nat.lt_succ_self _⟩, rfl⟩
  simpa [W, K, hspan i (by omega)] using hnext hq

end ConnGouldToint.Chapter05
