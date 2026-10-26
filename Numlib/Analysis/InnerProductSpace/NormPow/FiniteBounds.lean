import Numlib.Analysis.InnerProductSpace.NormPow.Smoothness

/-!
# Finite families of homogeneous norm-power derivative bounds

A common positive constant controls finitely many actual derivative operator
norms off the origin. Whenever the exponent exceeds the lower derivative
orders, their genuine vanishing values extend the estimate through zero.
-/

open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A fixed finite family of actual norm-power derivative operator norms has
one positive homogeneous bound, chosen before the order and the point. -/
theorem exists_common_normRpow_derivative_bound (lam : ℝ) (m : ℕ) :
    ∃ K > 0, ∀ j ≤ m, ∀ x : E, x ≠ 0 →
      ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x‖ ≤ K * ‖x‖ ^ (lam - j) := by
  classical
  choose C hC hb using fun j => exists_norm_iteratedFDeriv_normRpow_le (E := E) lam j
  let K := 1 + ∑ j ∈ Finset.range (m + 1), C j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (m + 1), C j :=
    Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro j hj x hx
  have hle : C j ≤ ∑ i ∈ Finset.range (m + 1), C i :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (by omega))
  exact (hb j x hx).trans (mul_le_mul_of_nonneg_right
    (by dsimp [K]; linarith : C j ≤ K) (Real.rpow_nonneg (norm_nonneg x) _))

/-- Orders below the exponent obey the homogeneous operator bound also at
the origin. The next derivative retains its valid off-origin bound. -/
theorem exists_global_normRpow_derivative_bound {lam : ℝ} {p : ℕ}
    (hp : (p : ℝ) < lam) :
    ∃ K > 0,
      (∀ j ≤ p, ∀ x : E,
        ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x‖ ≤ K * ‖x‖ ^ (lam - j)) ∧
      (∀ x : E, x ≠ 0 → ‖iteratedFDeriv ℝ (p + 1) (fun z : E => ‖z‖ ^ lam) x‖ ≤
        K * ‖x‖ ^ (lam - (p + 1))) := by
  obtain ⟨K, hK, hb⟩ := exists_common_normRpow_derivative_bound (E := E) lam (p + 1)
  refine ⟨K, hK, ?_, fun x hx => ?_⟩
  rotate_left
  · simpa only [Nat.cast_add, Nat.cast_one] using hb (p + 1) le_rfl x hx
  intro j hj x
  by_cases hx : x = 0
  · subst x
    rw [iteratedFDeriv_normRpow_zero_of_lt
      (show (j : ℝ) < lam from (show (j : ℝ) ≤ p by exact_mod_cast hj).trans_lt hp), norm_zero]
    positivity
  · exact hb j (by omega) x hx
