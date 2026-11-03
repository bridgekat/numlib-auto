import Mathlib.Basic.Real.Basic
import Numlib.Krylov.Lanczos

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


open scoped RealInnerProductSpace

/-- Algorithms 5.2.1 and 5.2.2 are the three-term symmetric Lanczos recurrence.
The initial unnormalized vector is the starting residual, and the preceding
basis vector at step zero is zero. -/
theorem algorithm_5_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {r₀ : E} (hr₀ : r₀ ≠ 0) (k : ℕ) :
    let q := Arnoldi.vec H r₀
    let y : ℕ → E := fun | 0 => r₀ | j + 1 => Arnoldi.w H r₀ j
    let prev : ℕ → E := fun | 0 => 0 | j + 1 => q j
    q k = ‖y k‖⁻¹ • y k ∧
      y (k + 1) = H (q k) - ⟪q k, H (q k)⟫ • q k - ‖y k‖ • prev k := by
  intro q y prev
  have hd (j : ℕ) : Lanczos.alpha H r₀ j = ⟪q j, H (q j)⟫ := by
    simp [Lanczos.alpha, Arnoldi.coeff, q]
  cases k with
  | zero =>
    refine ⟨by simpa using Arnoldi.vec_zero H r₀ hr₀, ?_⟩
    change Arnoldi.w H r₀ 0 = H (q 0) - ⟪q 0, H (q 0)⟫ • q 0 - ‖r₀‖ • (0 : E)
    have ha : H (q 0) = Lanczos.alpha H r₀ 0 • q 0 + Arnoldi.w H r₀ 0 := by
      have h := Lanczos.apply_vec_zero r₀ hH
      rw [Lanczos.beta, ← Arnoldi.w_eq_norm_smul_vec] at h
      simpa only [q, RCLike.ofReal_real_eq_id, id_eq] using h
    rw [← hd, ha, smul_zero, sub_zero]
    abel
  | succ j =>
    refine ⟨by simpa using Arnoldi.vec_succ_eq H r₀ j, ?_⟩
    change Arnoldi.w H r₀ (j + 1) = H (q (j + 1)) - ⟪q (j + 1), H (q (j + 1))⟫ •
      q (j + 1) - ‖Arnoldi.w H r₀ j‖ • q j
    simpa only [q, hd, Lanczos.beta, RCLike.ofReal_real_eq_id, id_eq] using Lanczos.w_succ_eq r₀ hH j

end ConnGouldToint.Chapter05
