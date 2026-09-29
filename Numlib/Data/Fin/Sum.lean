/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.BigOperators.Fin` and `Mathlib.Logic.Equiv.Fin.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Splitting `Fin` at an index

Three ways of cutting `Fin` into a head and a tail, each the form some matrix argument needs:

* `finSumFinEquiv_symm_cases`: an index of `Fin (s + m)` comes from the left summand of
  `Fin s ⊕ Fin m` when it is below `s`, and from the right one, shifted by `s`, otherwise — the case
  split behind every computation with `fromBlocks` reindexed along `finSumFinEquiv`.
* `Matrix.sum_fin_eq_sum_castLE_add_sum_Ioi`: a sum over `Fin k` is the sum over the leading
  `j + 1` indices, read through `Fin.castLE`, plus the sum over the indices after `j`.
* `Fin.sum_castLE_eq_sum_ite`: a sum over `Fin k` read through `Fin.castLE` into `Fin a` is the sum
  over `Fin a` of the terms below `k`.
-/

open Finset

/-- The two halves of `Fin (s + m)` under `finSumFinEquiv`: an index below `s` comes from the left
summand, an index from `s` on from the right one, shifted by `s`. -/
theorem finSumFinEquiv_symm_cases {s m : ℕ} (i : Fin (s + m)) :
    (∃ hi : (i : ℕ) < s, finSumFinEquiv.symm i = Sum.inl ⟨i, hi⟩) ∨
      ∃ hi : s ≤ (i : ℕ), finSumFinEquiv.symm i = Sum.inr ⟨i - s, by omega⟩ := by
  by_cases hi : (i : ℕ) < s
  · refine Or.inl ⟨hi, finSumFinEquiv.symm_apply_eq.2 ?_⟩
    rw [finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  · refine Or.inr ⟨not_lt.1 hi, finSumFinEquiv.symm_apply_eq.2 ?_⟩
    rw [finSumFinEquiv_apply_right]
    exact Fin.ext (by simp; omega)

/-- Splitting a sum over `Fin k` at `j`: the leading `j + 1` indices, read through `Fin.castLE`,
and the indices after `j`. -/
theorem Matrix.sum_fin_eq_sum_castLE_add_sum_Ioi {M : Type*} [AddCommMonoid M] {k : ℕ}
    (j : Fin k) (g : Fin k → M) :
    ∑ i, g i = ∑ a : Fin (j + 1), g (Fin.castLE j.isLt a) + ∑ i ∈ Ioi j, g i := by
  rw [← sum_filter_add_sum_filter_not univ (· ≤ j)]
  congr 1
  · refine (sum_bij (fun a _ => Fin.castLE j.isLt a) (fun a _ => ?_)
      (fun a _ b _ hab => Fin.castLE_injective _ hab) (fun i hi => ?_) (fun _ _ => rfl)).symm
    · simp only [mem_filter, mem_univ, true_and, Fin.le_def, Fin.val_castLE]
      have := a.isLt
      omega
    · simp only [mem_filter, mem_univ, true_and, Fin.le_def] at hi
      exact ⟨⟨i, by omega⟩, mem_univ _, Fin.ext (by simp)⟩
  · refine sum_congr ?_ fun _ _ => rfl
    ext i
    simp

/-- A sum over `Fin k`, read through `Fin.castLE` into `Fin a` for `k ≤ a`, is the sum over `Fin a`
of the terms below `k`: the reindexing between `Fin (min m n)` and the indices of a rectangular
diagonal. -/
theorem Fin.sum_castLE_eq_sum_ite {M : Type*} [AddCommMonoid M] {k a : ℕ} (hk : k ≤ a)
    (g : Fin a → M) :
    ∑ i : Fin k, g (Fin.castLE hk i) = ∑ i : Fin a, if (i : ℕ) < k then g i else 0 := by
  classical
  set g' : ℕ → M := fun j => if h : j < a then g ⟨j, h⟩ else 0 with hg'
  have h1 : ∀ i : Fin k, g (Fin.castLE hk i) = g' i := fun i => by
    simp [hg', Fin.castLE, lt_of_lt_of_le i.isLt hk]
  have h2 : ∀ i : Fin a, (if (i : ℕ) < k then g i else 0) = if (i : ℕ) < k then g' i else 0 :=
    fun i => by simp [hg', i.isLt]
  simp_rw [h1, h2]
  rw [Fin.sum_univ_eq_sum_range (fun i => g' i) k,
    Fin.sum_univ_eq_sum_range (fun i => if i < k then g' i else 0) a, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  omega
